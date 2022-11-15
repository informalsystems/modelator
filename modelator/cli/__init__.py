import os
import time
from pathlib import Path
from timeit import default_timer as timer
from typing import Dict, List, Optional

import semver
import typer

from modelator import ModelResult, __version__, const_values
from modelator.cli.model_config_file import load_config_file
from modelator.cli.model_file import ModelFile
from modelator.itf import ITF
from modelator.Model import Model
from modelator.utils import apalache_jar, tla_helpers
from modelator.utils.model_exceptions import ModelParsingError, ModelTypecheckingError

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


def _create_and_parse_model(
    model_path: str, init="Init", next="Next", constants={}, *, args: Dict[str, str]
):
    try:
        model = Model(model_path, init, next, constants=constants)
    except ValueError:
        print("ERROR: file not found ❌")
        return

    model.files_contents = tla_helpers.get_auxiliary_tla_files(model_path)

    try:
        model.parse(args=args)
    except ModelParsingError as e:
        print("Parsing error 💥")
        print(e)
        raise typer.Exit(code=5)

    return model


@app.command(
    context_settings={"allow_extra_args": True, "ignore_unknown_options": True}
)
def load(
    ctx: typer.Context,
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
    extra_args = [arg[2:] for arg in ctx.args if arg.startswith("--")]
    extra_args = _parse_list_of_assignments(extra_args)
    model = _create_and_parse_model(path, args=extra_args)

    config = None
    if config_path:
        print(f"Loading {config_path}... ")
        try:
            config = load_config_file(config_path)
        except FileNotFoundError:
            print("ERROR: config file not found")
            raise typer.Exit(code=4)

    ModelFile.save(model, config, config_path)
    print("Loading OK ✅")


@app.command(
    context_settings={"allow_extra_args": True, "ignore_unknown_options": True}
)
def reload(
    ctx: typer.Context,
):
    """
    Reload model and configuration files, if any.
    """
    model, config, config_path = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("ERROR: model not loaded; run `modelator load` first")
        return

    model_path = model.tla_file_path

    print(f"Reloading {model_path}... ")
    extra_args = [arg[2:] for arg in ctx.args if arg.startswith("--")]
    extra_args = _parse_list_of_assignments(extra_args)
    model = _create_and_parse_model(model_path, args=extra_args)

    if config_path:
        print(f"Loading {config_path}... ")
        try:
            config = load_config_file(config_path)
        except FileNotFoundError:
            print("ERROR: config file not found")
            raise typer.Exit(code=4)

    ModelFile.save(model, config, config_path)
    print("Loading OK ✅")


@app.command(
    context_settings={"allow_extra_args": True, "ignore_unknown_options": True}
)
def typecheck(
    ctx: typer.Context,
):
    """
    Type check the loaded model, if available.
    """
    global LOG_LEVEL
    model, _, _ = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("Model file does not exist")
        return

    try:
        extra_args = [arg[2:] for arg in ctx.args if arg.startswith("--")]
        extra_args = _parse_list_of_assignments(extra_args)

        model.typecheck(extra_args)
        print("Type checking OK ✅")
    except ModelTypecheckingError as e:
        print("Type checking error 💥")
        print(e)
        raise typer.Exit(code=6)


@app.command(
    context_settings={"allow_extra_args": True, "ignore_unknown_options": True}
)
def simulate(
    ctx: typer.Context,
    model_path: Optional[str] = typer.Option(None, help="Path to the TLA+ model file."),
    config_path: Optional[str] = typer.Option(
        None, help="Path to TOML file with model and model checker configurations."
    ),
    init: Optional[str] = typer.Option(None, help="Model's init predicate."),
    next: Optional[str] = typer.Option(None, help="Model's next predicate."),
    constants: Optional[str] = typer.Option(
        None,
        help="Comma-separated list of constant definitions in the format 'name=value' (overwrites config file).",
    ),
    length: Optional[int] = typer.Option(
        default=10, help="Number of steps in each simulation"
    ),
    max_trace: Optional[int] = typer.Option(
        default=5, help="Number of simulated traces to generate."
    ),
    traces_dir: Optional[str] = typer.Option(
        None,
        help="Path to store generated trace files (overwrites config file).",
    ),
):
    """
    Generate execution traces by simulating the model evolution.
    """
    model, config = _load_model_with_arguments(
        "simulate",
        None,
        model_path,
        config_path,
        init,
        next,
        constants,
        traces_dir,
        ctx.args,
    )

    config["params"]["output_traces"] = True
    config["params"]["length"] = length
    config["params"]["max_run"] = max_trace

    _run_checker("simulate", model, config)


@app.command(
    context_settings={"allow_extra_args": True, "ignore_unknown_options": True}
)
def check(
    ctx: typer.Context,
    model_path: Optional[str] = typer.Option(None, help="Path to the TLA+ model file."),
    config_path: Optional[str] = typer.Option(
        None, help="Path to TOML file with model and model checker configurations."
    ),
    init: Optional[str] = typer.Option(None, help="Model's init predicate."),
    next: Optional[str] = typer.Option(None, help="Model's next predicate."),
    constants: Optional[str] = typer.Option(
        None,
        help="Comma-separated list of constant definitions in the format 'name=value' (overwrites config file).",
    ),
    invariants: Optional[str] = typer.Option(
        None,
        help="Comma-separated list of invariants to check (overwrites config file).",
    ),
    traces_dir: Optional[str] = typer.Option(
        None,
        help="Path to store generated trace files (overwrites config file).",
    ),
):
    """
    Check that the invariants hold in the model, or generate a trace for a counterexample.

    If extra options are provided, they will be passed directly to the model-checker,
    overwriting values in the config file.
    """
    model, config = _load_model_with_arguments(
        "check",
        invariants,
        model_path,
        config_path,
        init,
        next,
        constants,
        traces_dir,
        ctx.args,
    )
    _run_checker("check", model, config)


@app.command(
    context_settings={"allow_extra_args": True, "ignore_unknown_options": True}
)
def sample(
    ctx: typer.Context,
    model_path: Optional[str] = typer.Option(None, help="Path to the TLA+ model file."),
    config_path: Optional[str] = typer.Option(
        None, help="Path to TOML file with model and model checker configurations."
    ),
    init: Optional[str] = typer.Option(None, help="Model's init predicate."),
    next: Optional[str] = typer.Option(None, help="Model's next predicate."),
    constants: Optional[str] = typer.Option(
        None,
        help="Comma-separated list of constant definitions in the format 'name=value' (overwrites config file).",
    ),
    tests: Optional[str] = typer.Option(
        None,
        help="Comma-separated list of model predicates describing desired properties in the final state of the execution (overwrites config file).",
    ),
    traces_dir: Optional[str] = typer.Option(
        None,
        help="Path to store generated trace files (overwrites config file).",
    ),
):
    """
    Generate execution traces that reach the state described by the `tests` properties.

    If extra options are provided, they will be passed directly to the model-checker,
    overwriting values in the config file.
    """
    model, config = _load_model_with_arguments(
        "sample",
        tests,
        model_path,
        config_path,
        init,
        next,
        constants,
        traces_dir,
        ctx.args,
    )
    _run_checker("sample", model, config)


def _parse_list(s: Optional[str]) -> List[str]:
    if s is None:
        return []
    try:
        return list(s.split(","))
    except ValueError:
        print(f"ERROR: cannot parse {s} as a comma-separated list of assignments")
        raise typer.Exit(code=1)


def _parse_list_of_assignments(list: List[str]) -> Dict[str, str]:
    try:
        return dict([c.split("=") for c in list])
    except ValueError:
        print(f"ERROR: cannot parse {list} as a list of assignments")
        raise typer.Exit(code=1)


def _load_config_and_merge_arguments(
    config_path,
    properties_config_name,
    properties,
    init,
    next,
    constants,
    traces_dir,
    extra_args,
):
    """
    Load a config file and merge it with the given arguments.
    """
    # Convert strings to lists and dicts
    properties = _parse_list(properties)

    constants = _parse_list(constants)
    constants = _parse_list_of_assignments(constants)

    extra_args = [arg[2:] for arg in extra_args if arg.startswith("--")]
    extra_args = _parse_list_of_assignments(extra_args)

    # Load config file
    try:
        config = load_config_file(config_path)
    except FileNotFoundError:
        print("ERROR: config file not found")
        raise typer.Exit(code=4)

    # Overwrite configuration with passed arguments
    config_from_arguments = {}
    if init:
        config_from_arguments["init"] = init
    if next:
        config_from_arguments["next"] = next
    if constants:
        config_from_arguments["constants"] = constants
    if properties:
        config_from_arguments[properties_config_name] = properties
    if traces_dir:
        config_from_arguments["traces_dir"] = traces_dir
    config = {**config, **config_from_arguments}

    # Update model-cheker arguments. Note that `extra_args` may contain any
    # field name, even some not supported in the toml configuration file.
    if extra_args:
        config["params"] = {**config["params"], **extra_args}
        config_from_arguments["params"] = extra_args

    return config, config_from_arguments


def _load_model_with_arguments(
    mode,
    properties,
    model_path,
    config_path,
    init,
    next,
    constants,
    traces_dir,
    extra_args,
):
    """
    Load a model from the given configuration file, or model path, or from pickle file.
    Merge the configuration with the given parameters.
    """
    if mode == "check":
        properties_config_name = "invariants"
    elif mode == "sample" or mode == "simulate":
        properties_config_name = "tests"
    else:
        raise ValueError("Unknown checker mode")

    if not traces_dir:
        timestamp = time.strftime("%Y%m%d-%H%M%S")
        traces_dir = os.path.join(const_values.DEFAULT_TRACES_DIR, timestamp)

    config, config_from_arguments = _load_config_and_merge_arguments(
        config_path,
        properties_config_name,
        properties,
        init,
        next,
        constants,
        traces_dir,
        extra_args,
    )

    model = None

    # Load a model from a given path...
    if model_path:
        model = _create_and_parse_model(
            model_path,
            config["init"],
            config["next"],
            config["constants"],
            args=config["params"],
        )

    # or load a model saved in a pickle file.
    if not model:
        model, saved_config, _ = ModelFile.load(LOG_LEVEL)
        if saved_config:
            config = {**config, **saved_config}
            config = {**config, **config_from_arguments}

    if not model:
        print(
            "ERROR: could not find a model; either:\n"
            "- load a model with `load <path/to/model/file>`, or\n"
            "- provide a path to a model file with --model-path\n"
        )
        raise typer.Exit(code=1)

    if (mode == "sample" or mode == "check") and not config[properties_config_name]:
        print(
            "ERROR: could not find properties to check; either:\n"
            "- load a configuration together with a model "
            "`load <path/to/model/file> --config <path/to/config/file>`, or\n"
            "- provide a path to a config file with --config-path, or\n"
            f"- provide a list of properties to check with --{properties_config_name}\n"
        )
        raise typer.Exit(code=2)

    # Check that the properties are defined in the model
    diff = set(config[properties_config_name]) - set(model.operators)
    if diff:
        print("ERROR: {} not defined in the model".format(", ".join(diff)))
        raise typer.Exit(code=3)

    return model, config


def _run_checker(mode, model, config):
    """
    Run the model checker given a model and a configuration.
    """
    model.init_predicate = config["init"]
    model.next_predicate = config["next"]

    if mode == "check":
        handler = model.check
        action = "Checking"
        properties_config_name = "invariants"
    elif mode == "sample":
        handler = model.sample
        action = "Sampling"
        properties_config_name = "tests"
    elif mode == "simulate":
        handler = model.simulate
        action = "Simulating"
        properties_config_name = "tests"
    else:
        raise ValueError("Unknown checker mode")

    start_time = timer()
    print("{} {}... ".format(action, ", ".join(config[properties_config_name])))
    result: ModelResult = handler(
        config[properties_config_name],
        checker_params=config["params"],
        constants=config["constants"],
        traces_dir=config["traces_dir"],
    )

    for itf_json_file in Path(config["traces_dir"]).glob("**/*.itf.json"):
        itf_trace = ITF.from_itf_json(itf_json_file)
        with open(itf_json_file.with_suffix(".md"), "w", encoding="utf-8") as f:
            f.write(ITF.markdown(itf_trace, diff=False))
        with open(itf_json_file.with_suffix(".diff.md"), "w", encoding="utf-8") as f:
            f.write(ITF.markdown(itf_trace, diff=True))

    print(f"Results:\n{result}")
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
        print("Model file removed")


@app.command()
def version():
    """
    Print current version of Modelator.
    """
    print(f"modelator {__version__}")


app_apalache = typer.Typer(
    name="apalache",
    help="Apalache: check whether the JAR file is locally available or download it.",
    no_args_is_help=True,
    add_completion=False,
    rich_markup_mode="rich",
)
app.add_typer(app_apalache, name="apalache")


@app_apalache.command(name="info")
def apalache_info(
    version: Optional[str] = typer.Argument(
        const_values.DEFAULT_APALACHE_VERSION, help="Apalache's version."
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
        print("Apalache JAR file not found")


def version_callback(value: str):
    try:
        semver.parse(value)
    except ValueError as e:
        raise typer.BadParameter(str(e))
    return value


@app_apalache.command()
def get(
    version: Optional[str] = typer.Argument(
        const_values.DEFAULT_APALACHE_VERSION,
        help="Apalache's version.",
        callback=version_callback,
    ),
):
    """
    Download Apalache jar file.
    """
    jar_path = apalache_jar.apalache_jar_build_path(
        const_values.DEFAULT_CHECKERS_LOCATION, version
    )
    if apalache_jar.apalache_jar_exists(jar_path, version):
        typer.confirm(
            f"Apalache version {version} already exists at {jar_path}\n"
            "Do you want to download it again?",
            abort=True,
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
