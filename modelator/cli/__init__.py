from pathlib import Path
from timeit import default_timer as timer
import typer
from typing import Dict, List, Optional

from modelator import ModelResult, const_values
from modelator.cli.model_config_file import load_config_file
from modelator.cli.model_file import ModelFile
from modelator.Model import Model
from modelator.utils import apalache_jar, tla_helpers
from modelator.utils.model_exceptions import ModelError

LOG_LEVEL = None


def set_log_level_callback(level: str):
    if not level:
        return
    global LOG_LEVEL
    LOG_LEVEL = level
    print(f"Log level set to {level}")


app = typer.Typer(
    name="modelator",
    help="Modelator: model-based testing framework for TLA+",
    no_args_is_help=True,
    add_completion=False,
    rich_markup_mode="rich",
)


@app.callback()
def common(
    ctx: typer.Context,
    log_level: str = typer.Option(None, "--log-level", callback=set_log_level_callback),
):
    pass


def _create_and_parse_model(model_path: str, init="Init", next="Next", constants={}):
    try:
        model = Model(model_path, init, next, constants=constants)
    except ValueError:
        print("ERROR: file not found ❌")
        return

    model.files_contents = tla_helpers.get_auxiliary_tla_files(model_path)
    model._parse()

    return model


def _print_results(result: ModelResult):
    print("Results:")
    for op in result.inprogress():
        print(f"⏳ {op}")
    for op in result.successful():
        print(f"✅ {op}")
        trace = result.traces(op)
        if trace:
            print(f"    Trace: {trace}")
        trace_paths = result.trace_paths(op)
        if trace_paths:
            print(f"    Trace files: {trace_paths}")
    for op in result.unsuccessful():
        print(f"❌ {op}")
        trace = result.traces(op)
        if trace:
            print(f"    Trace: {trace}")
        trace_paths = result.trace_paths(op)
        if trace_paths:
            print(f"    Trace files: {trace_paths}")


@app.command()
def load(
    path: str = typer.Argument(..., help="Path to a TLA+ model file."),
    config_path: Optional[str] = typer.Option(
        None,
        "--config",
        help="Path to a TOML configuration file.",
    ),
):
    """
    Load a TLA+ model file and parses it.
    """
    if not Path(path).is_file():
        print("ERROR: file does not exist")
        return

    if ModelFile.exists():
        typer.confirm(
            "A model is already loaded and it will be overwritten. "
            "Are you sure you want to continue?",
            abort=True,
        )

    print(f"Loading {path}... ")
    model = _create_and_parse_model(path)

    config = None
    if config_path:
        print(f"Loading {config_path}... ")
        config = load_config_file(config_path)

    ModelFile.save(model, config, config_path)
    print("Loading OK ✅")


@app.command()
def reload():
    """
    Reload model and configuration files, if any.
    """
    model, config, config_path = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("ERROR: model not loaded; run `modelator load` first")
        return

    model_path = model.tla_file_path

    print(f"Reloading {model_path}... ")
    model = _create_and_parse_model(model_path)

    if config_path:
        print(f"Loading {config_path}... ")
        config = load_config_file(config_path)

    ModelFile.save(model, config, config_path)
    print("Loading OK ✅")


@app.command()
def typecheck():
    """
    Type check the loaded model, if available.
    """
    global LOG_LEVEL
    model, _, _ = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("Model file does not exist")
        return

    try:
        model.typecheck()
        print("Type checking OK ✅")
    except ModelError as e:
        print("Type checking error 💥")
        print(e)


@app.command(
    # context_settings={"allow_extra_args": True, "ignore_unknown_options": True}
)
def check(
    # ctx: typer.Context,
    model_path: Optional[str] = typer.Option(None, help="Path to the TLA+ model file."),
    config_path: Optional[str] = typer.Option(
        None, help="Path to TOML file with model and model checker configurations."
    ),
    constants: Optional[List[str]] = typer.Option(
        None,
        help="Constant definitions in the format 'name=value' (overwrites config file).",
    ),
    invariants: Optional[List[str]] = typer.Option(
        None, help="List of invariants to check (overwrites config file)."
    ),
    params: Optional[List[str]] = typer.Option(
        None,
        help="Extra parameters to be passed to the model-checker (overwrites config file).",
    ),
    traces_dir: Optional[str] = typer.Option(
        None, help="Path to store generated trace files (overwrites config file)."
    ),
):
    """
    Check that the invariants hold in the model, or generate a trace for a counterexample.
    """
    # for extra_arg in ctx.args:
    #     print(f"Got extra arg: {extra_arg}")
    model, config = _load_model_with_params(
        "check", invariants, model_path, config_path, constants, params, traces_dir
    )
    _run_cheker("check", model, config)


@app.command()
def sample(
    model_path: Optional[str] = typer.Option(None, help="Path to the TLA+ model file."),
    config_path: Optional[str] = typer.Option(
        None, help="Path to TOML file with model and model checker configurations."
    ),
    constants: Optional[List[str]] = typer.Option(
        None,
        help="Constant definitions in the format 'key=value' (overwrites config file).",
    ),
    examples: Optional[List[str]] = typer.Option(
        None,
        help="Model operators describing desired properties in the final state of the execution (overwrites config file).",
    ),
    params: Optional[List[str]] = typer.Option(
        None,
        help="Extra parameters to be passed to the model-checker (overwrites config file).",
    ),
    traces_dir: Optional[str] = typer.Option(
        None, help="Path to store generated trace files (overwrites config file)."
    ),
):
    """
    Generate execution traces that reach the state described by the `examples` properties.
    """
    model, config = _load_model_with_params(
        "sample", examples, model_path, config_path, constants, params, traces_dir
    )
    _run_cheker("sample", model, config)


def _parse_list_of_assignments(list: List[str]) -> Dict[str, str]:
    try:
        return dict([c.split("=") for c in list])
    except ValueError:
        print(f"ERROR: cannot parse {list} as a ;-separated list of assignments")
        raise typer.Exit(code=1)


def _load_model_with_params(
    mode, properties, model_path, config_path, constants, params, traces_dir
):
    """
    Load a model from the given configuration file, or model path, or from pickle file.
    Merge the configuration with the given parameters.
    """
    if mode == "check":
        properties_config_name = "invariants"
    elif mode == "sample":
        properties_config_name = "examples"
    else:
        raise ValueError("Unknown checker mode")

    # Convert lists to dicts
    constants = _parse_list_of_assignments(constants)
    params = _parse_list_of_assignments(params)

    config = load_config_file(config_path)

    # Overwrite configuration with passed arguments
    config_from_arguments = {}
    if constants:
        config_from_arguments["constants"] = constants
    if properties:
        config_from_arguments[properties_config_name] = properties
    if traces_dir:
        config_from_arguments["traces_dir"] = traces_dir
    config = config | config_from_arguments

    # Note that the `params` may contain fields not available in the configuration.
    config["params"] = config["params"] | params

    model = None
    # load a model from a given path
    if model_path:
        model = _create_and_parse_model(
            model_path, config["init"], config["next"], config["constants"]
        )

    # or load a model saved in a pickle file
    if not model:
        model, saved_config, _ = ModelFile.load(LOG_LEVEL)
        if saved_config:
            config = config | saved_config | config_from_arguments

    if not model:
        print("ERROR: could not find a model; either:")
        print("- load a model with `load <path/to/model/file>`, or")
        print("- provide a path to a model file with --model-path")
        raise typer.Exit(code=1)

    if not config[properties_config_name]:
        print("ERROR: could not find properties to check; either:")
        print(
            "- load a configuration together with a model `load <path/to/model/file> --config <path/to/config/file>`, or"
        )
        print("- provide a path to a config file with --config-path, or")
        print("- provide a list of properties to check with --invariants")
        raise typer.Exit(code=2)

    diff = set(config[properties_config_name]) - set(model.operators)
    if diff:
        print("ERROR: {} not defined in the model".format(", ".join(diff)))
        raise typer.Exit(code=3)

    return model, config


def _run_cheker(mode, model, config):
    """
    Run the model checker given a model and a configuration.
    """
    print(config["init"])
    model.init_predicate = config["init"]
    model.next_predicate = config["next"]

    if mode == "check":
        handler = model.check
        action = "Checking"
        properties_config_name = "invariants"
    elif mode == "sample":
        handler = model.sample
        action = "Sampling"
        properties_config_name = "examples"
    else:
        raise ValueError("Unknown checker mode")

    start_time = timer()
    print("{} {}... ".format(action, ", ".join(config[properties_config_name])))
    result = handler(
        config[properties_config_name],
        constants=config["constants"],
        checker_params=config["params"],
        traces_dir=config["traces_dir"],
    )
    _print_results(result)
    print(f"Total time: {(timer() - start_time):.2f} seconds")


@app.command()
def info():
    """
    Display information on the loaded model, if available.
    """
    global LOG_LEVEL
    model, config, config_path = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("Model file does not exist")
        return

    print("Model:")
    for k, v in sorted(model.info().items()):
        print(f"- {k}: {v}")

    if config:
        print(f"Config at {config_path}:")
        for k, v in sorted(config.items()):
            print(f"- {k}: {v}")


@app.command()
def reset():
    """
    Removes any loaded model.
    """
    if ModelFile.clean():
        print(f"Model file removed")


app_apalache = typer.Typer(
    name="apalache",
    help="Apalache: check whether the JAR file is locally available or download it.",
    no_args_is_help=True,
    add_completion=False,
    rich_markup_mode="rich",
)
app.add_typer(app_apalache, name="apalache")


@app_apalache.command()
def info(
    version: Optional[str] = typer.Argument(
        const_values.DEFAULT_APALACHE_VERSION, help=f"Apalache's version."
    ),
):
    """
    Display whether Apalache is installed and information about it.
    """
    print(f"Default location for JAR file: {const_values.DEFAULT_CHECKERS_LOCATION}")
    print(f"Looking for version: {version}")
    jar_path = apalache_jar.apalache_jar_build_path(
        const_values.DEFAULT_CHECKERS_LOCATION, version
    )
    print(f"Looking for file: {jar_path}")
    if apalache_jar.apalache_jar_exists(jar_path, version):
        existing_version = apalache_jar.apalache_jar_version(jar_path)
        print(f"Apalache JAR file exists and its version is {existing_version}")
    else:
        print(f"Apalache JAR file not found")


@app_apalache.command()
def get(
    version: Optional[str] = typer.Argument(
        const_values.DEFAULT_APALACHE_VERSION, help=f"Apalache's version."
    ),
):
    """
    Download Apalache jar file.
    """
    jar_path = apalache_jar.apalache_jar_build_path(
        const_values.DEFAULT_CHECKERS_LOCATION, version
    )
    print(f"Downloading Apalache version {version}")
    try:
        apalache_jar.apalache_jar_download(
            download_location=const_values.DEFAULT_CHECKERS_LOCATION,
            expected_version=version,
        )
        print("Done ✅")
        print(f"Apalache jar file: {jar_path}")
    except ValueError as e:
        print(f"ERROR: {e}")
