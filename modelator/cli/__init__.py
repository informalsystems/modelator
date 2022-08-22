from pathlib import Path
from timeit import default_timer as timer
import typer
from typing import Dict, List, Optional, Tuple

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


def _load_model(
    model_path: Optional[str], init="Init", next="Next", constants={}
) -> Tuple[Optional[Model], Optional[Dict]]:
    global LOG_LEVEL
    config = None
    if model_path is None:
        model, config = ModelFile.load(LOG_LEVEL)
        if model is None:
            print("Model file does not exist")
            return None, None
    else:
        model = _create_and_parse_model(model_path, init, next, constants)

    return model, config


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
    path: str = typer.Argument(
        ..., help="Path to TLA+ model file or to TOML configuration file."
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
            "A model is already loaded and it will be overwritten."
            "Are you sure you want to continue?",
            abort=True,
        )

    if Path(path).suffix == ".toml":
        config = load_config_file(path)
        model_path = config["model_path"]
    else:
        config = None
        model_path = path

    print(f"Loading {model_path}... ")
    model = _create_and_parse_model(model_path)
    ModelFile.save(model, config)
    print("Loading OK ✅")


@app.command()
def reload():
    """
    Reload current model, if any.
    """
    model, config = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("ERROR: model not loaded; run `modelator load` first")
        return

    model_path = model.tla_file_path

    print(f"Reloading {model_path}... ")
    model = _create_and_parse_model(model_path)
    ModelFile.save(model, config)
    print("Loading OK ✅")


@app.command()
def typecheck():
    """
    Type check the loaded model, if available.
    """
    global LOG_LEVEL
    model, _ = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("Model file does not exist")
        return

    try:
        model.typecheck()
        print("Type checking OK ✅")
    except ModelError as e:
        print("Type checking error 💥")
        print(e)


def _run_checker(mode, properties, config_path, model_path, constants, params, traces_dir):
    if mode == "check":
        properties_config_name = "invariants"
    elif mode == "sample":
        properties_config_name = "examples"
    else:
        raise ValueError("Unknown checker mode")

    # Convert lists to dicts
    constants = dict([c.split("=") for c in constants])
    params = dict([p.split("=") for p in params])

    config = load_config_file(config_path)

    # Overwrite configuration with parameters
    if model_path:
        config["model_path"] = model_path
    if constants:
        config["constants"] = constants    
    if properties:
        config[properties_config_name] = properties
    if traces_dir:
        config["traces_dir"] = traces_dir
    
    # Note that the `params` may contain fields not available in the configuration.
    config["params"] = params | config["params"]

    model = None
    if model_path:
        model = _create_and_parse_model(model_path, config["init"], config["next"], config["constants"])

    if not model:
        model, saved_config = ModelFile.load(LOG_LEVEL)
        if saved_config:
            config = config | saved_config

    if not model or not config[properties_config_name]:
        print("ERROR: could not find a model and a configuration with properties to check; either:")
        print("- specify a path to a config file with --config-path, or")
        print("- load a model from a config file with `load <path/to/config/file>`, or")
        print("- load a model from a TLA+ file and specify --invariants")
        if config['model_path']:
            print(f"\nPath to model file: {config['model_path']}")
        raise typer.Exit(code=1)

    diff = set(config[properties_config_name]) - set(model.operators)
    if diff:
        print("ERROR: {} not defined in the model".format(", ".join(diff)))
        raise typer.Exit(code=1)

    if mode == "check":
        handler = model.check
        action = "Checking"
    elif mode == "sample":
        handler = model.sample
        action = "Sampling"
    else:
        raise ValueError("Unknown checker mode")

    start_time = timer()
    print("{} {}... ".format(action, ", ".join(config[properties_config_name])))
    result = handler(
        config[properties_config_name], 
        constants=config["constants"], 
        checker_params=config["params"], 
        traces_dir=config["traces_dir"]
    )
    _print_results(result)
    print(f"Total time: {(timer() - start_time):.2f} seconds")


@app.command()
def check(
    config_path: Optional[str] = typer.Option(
        None, help="Path to TOML file with the model and model checker configuration."
    ),
    model_path: Optional[str] = typer.Option(
        None, help="Path to the TLA+ model file (overwrites config file)."
    ),
    constants: Optional[List[str]] = typer.Option(
        None,
        help="Constant definitions in the format 'name=value' (overwrites config file).",
    ),
    invariants: Optional[List[str]] = typer.Option(
        None, help="List of invariants to check (overwrites config file)."
    ),
    params: Optional[List[str]] = typer.Option(
        None, help="Extra parameters to be passed to the model-checker."
    ),
    traces_dir: Optional[str] = typer.Option(
        None, help="Path to store generated trace files (overwrites config file)."
    ),
):
    """
    Check that the invariants hold in the model, or generate a trace for a counterexample.
    """
    _run_checker("check", invariants, config_path, model_path, constants, params, traces_dir)


@app.command()
def sample(
    config_path: Optional[str] = typer.Option(
        None, help="Path to TOML file with the model and model checker configuration."
    ),
    model_path: Optional[str] = typer.Option(
        None, help="Path to the TLA+ model file (overwrites config file)."
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
        None, help="Extra parameters to be passed to the model-checker."
    ),
    traces_dir: Optional[str] = typer.Option(
        None, help="Path to store generated trace files (overwrites config file)."
    ),
):
    """
    Generate execution traces that reach the state described by the `examples` properties.
    """
    _run_checker("sample", examples, config_path, model_path, constants, params, traces_dir)


@app.command()
def info():
    """
    Display information on the loaded model, if available.
    """
    global LOG_LEVEL
    model, config = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("Model file does not exist")
        return

    print("Model:")
    for k, v in sorted(model.info().items()):
        print(f"- {k}: {v}")

    if config:
        print("Config:")
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
