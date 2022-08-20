from pathlib import Path
import typer
from timeit import default_timer as timer
from typing import List, Optional

import typer

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
) -> Optional[Model]:
    global LOG_LEVEL
    if model_path is None:
        model = ModelFile.load(LOG_LEVEL)
        if model is None:
            print("Model file does not exist")
            return None
    else:
        model = _create_and_parse_model(model_path, init, next, constants)

    return model


def _print_results(result: ModelResult):
    print("Check results:")
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

    model_path = path
    # if path corresponds to a config file, use model_path from the config
    if Path(path).suffix == ".toml":
        config = load_config_file(path)
        model_path = config["model_path"]

    print(f"Loading {model_path}... ")
    model = _create_and_parse_model(model_path)
    ModelFile.save(model)
    print("Loading OK ✅")


@app.command()
def reload():
    """
    Reload current model, if any.
    """
    model = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("ERROR: model not loaded; run `modelator load` first")
        return

    model_path = model.tla_file_path

    print(f"Reloading {model_path}... ")
    model = _create_and_parse_model(model_path)
    ModelFile.save(model)
    print("Loading OK ✅")


@app.command()
def reload():
    """
    Reload current model, if any.
    """
    model = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("ERROR: model not loaded; run `modelator load` first")
        return

    model_path = model.tla_file_path

    print(f"Reloading {model_path}... ")
    model = _create_and_parse_model(model_path)
    ModelFile.save(model)
    print("Loading OK ✅")


@app.command()
def typecheck():
    """
    Type check the loaded model, if available.
    """
    global LOG_LEVEL
    model = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("Model file does not exist")
        return

    try:
        model.typecheck()
        print("Type checking OK ✅")
    except ModelError as e:
        print("Type checking error 💥")
        print(e)


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
    traces_dir: Optional[str] = typer.Option(
        None, help="Path to store generated trace files (overwrites config file)."
    ),
    params: Optional[List[str]] = typer.Option(
        None, help="Extra parameters to be passed to the model-checker."
    ),
):
    """
    Check that the invariants hold in the model, or generate a trace for a counterexample.
    """
    mc_invariants = invariants
    if config_path is None and mc_invariants == []:
        print("ERROR: either --config-path or --invariants must be specified.")
        raise typer.Exit(code=1)

    # Dict is not supported by typer
    constants = dict([c.split("=") for c in constants])
    params = dict([p.split("=") for p in params])

    config = load_config_file(config_path)
    model_path = model_path if model_path else config["model_path"]
    constants = constants if constants else config["constants"]
    mc_invariants = mc_invariants if mc_invariants else config["invariants"]
    traces_dir = traces_dir if traces_dir else config["traces_dir"]
    init = config["init"]
    next = config["next"]
    
    # Note that the `params` may contain fields not available in the configuration.
    params = params | config["params"]

    model = _load_model(model_path, init, next, constants)
    if model is None:
        return

    start_time = timer()
    result = model.check(mc_invariants, constants, checker_params=params, traces_dir=traces_dir)
    _print_results(result)
    print(f"Total time: {(timer() - start_time):.2f} seconds")


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
    traces_dir: Optional[str] = typer.Option(
        None, help="Path to store generated trace files (overwrites config file)."
    ),
):
    """
    Generate execution traces that reach the state described by the `examples` properties.
    """
    mc_invariants = examples
    if config_path is None and mc_invariants == []:
        print("ERROR: either --config-path or --desired-states must be specified.")
        raise typer.Exit(code=1)

    # Dict is not supported by typer
    constants = dict([c.split("=") for c in constants])
    params = dict([p.split("=") for p in params])

    config = load_config_file(config_path)
    model_path = model_path if model_path else config["model_path"]
    constants = constants if constants else config["constants"]
    mc_invariants = mc_invariants if mc_invariants else config["invariants"]
    traces_dir = traces_dir if traces_dir else config["traces_dir"]
    init = config["init"]
    next = config["next"]

    # Note that the `params` may contain fields not available in the configuration.
    params = params | config["params"]

    model = _load_model(model_path, init, next, constants)
    if model is None:
        return

    start_time = timer()
    result = model.sample(mc_invariants, constants, checker_params=params, traces_dir=traces_dir)
    _print_results(result)
    print(f"Total time: {(timer() - start_time):.2f} seconds")


@app.command()
def info():
    """
    Display information on the loaded model, if available.
    """
    global LOG_LEVEL
    model = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("Model file does not exist")
        return

    for k, v in model.info().items():
        print(f"# {k}: {v}")


@app.command()
def reset():
    """
    Removes any loaded model.
    """
    if ModelFile.clean():
        print(f"Model file removed")


@app.command()
def check_apalache_jar(
    version: Optional[str] = typer.Argument(
        const_values.DEFAULT_APALACHE_VERSION, help=f"Apalache's version."
    ),
):
    """
    Check whether Apalache's uber jar file is installed, or download it otherwise.
    """
    jar_path = apalache_jar.apalache_jar_build_path(
        const_values.DEFAULT_CHECKERS_LOCATION, version
    )
    if apalache_jar.apalache_jar_exists(jar_path, version):
        print(f"Apalache jar file exists at {jar_path}")
        existing_version = apalache_jar.apalache_jar_version(jar_path)
        print(f"Apalache jar version: {existing_version}")
    else:
        print(f"Apalache jar file not found at {jar_path}")
        print(f"Will attempt to download version {version}...")
        try:
            apalache_jar.apalache_jar_download(
                download_location=const_values.DEFAULT_CHECKERS_LOCATION,
                expected_version=version,
            )
            print("Done ✅")
            print(f"Apalache jar file: {jar_path}")
        except ValueError as e:
            print(f"ERROR: {e}")
