import typer
from typing import List, Optional
from timeit import default_timer as timer

from modelator.Model import Model
from modelator import ModelResult
from modelator.cli.model_config_file import load_config_file
from modelator.cli.model_file import ModelFile
from modelator.utils import tla_helpers
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


def _create_and_parse_model(model_path: str, init='Init', next='Next', constants={}):
    try:
        model = Model(model_path, init, next, constants=constants)
    except ValueError:
        print("❌ ERROR: file not found")
        return

    model.files_contents = tla_helpers.get_auxiliary_tla_files(model_path)
    model._parse()

    return model


def _load_model(model_path: Optional[str], init='Init', next='Next', constants={}) -> Optional[Model]:
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
def load(model_path: Optional[str] = typer.Argument(None, help="Path to TLA+ model file (if empty, will reload current model).")):
    '''
    Load a TLA+ model file and parses it.
    If no model path is provided, reload the current model, if any.
    '''
    if ModelFile.exists():
        print('WARNING: a model already exists and it will be overwritten')

    if model_path is None:
        # reload current model
        model = ModelFile.load(LOG_LEVEL)
        if model is None:
            print("Model file does not exist")
            return
        
        model_path = model.tla_file_path

    print(f"Loading {model_path}... ")
    model = _create_and_parse_model(model_path)
    ModelFile.save(model)
    print('Loading OK ✅')


@app.command()
def typecheck():
    '''
    Type check the loaded model, if available.
    '''
    global LOG_LEVEL
    model = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("Model file does not exist")
        return
    
    try:
        model.typecheck()
        print('Type checking OK ✅')
    except ModelError as e:
        print('Type checking error 💥')
        print(e)


@app.command()
def check(
    config_path: Optional[str] = typer.Option(None, help="Path to TOML file with the model and model checker configuration."), 
    model_path: Optional[str] = typer.Option(None, help="Path to the TLA+ model file (overwrites config file)."),
    constants: Optional[List[str]] = typer.Option(None, help="Constant definitions in the format 'name=value' (overwrites config file)."), 
    invariants: Optional[List[str]] = typer.Option(None, help="List of invariants to check (overwrites config file)."),  
    traces_dir: Optional[str] = typer.Option(None, help="Path to store generated trace files (overwrites config file)."),
):
    '''
    Check that the invariants hold in the model, or generate a trace for a counterexample.
    '''
    mc_invariants = invariants
    if config_path is None and mc_invariants == []:
        print("Error: either --config-path or --invariants must be specified.")
        raise typer.Exit(code=1)

    # Dict is not supported by typer
    constants = dict([c.split("=") for c in constants])

    config = load_config_file(config_path)
    model_path = config['model_path'] if model_path is None else model_path
    constants = config['constants'] if constants is None else constants
    mc_invariants = config['invariants'] if mc_invariants is None else mc_invariants
    init = config['init']
    next = config['next']
    traces_dir = config['traces_dir'] if traces_dir is None else traces_dir

    model = _load_model(model_path, init, next, constants)
    if model is None:
        return    
    
    start_time = timer()
    result = model.check(mc_invariants, constants, traces_dir=traces_dir)
    _print_results(result)
    print(f"Total time: {(timer() - start_time):.2f} seconds")


@app.command()
def sample(
    config_path: Optional[str] = typer.Option(None, help="Path to TOML file with the model and model checker configuration."), 
    model_path: Optional[str] = typer.Option(None, help="Path to the TLA+ model file (overwrites config file)."),
    constants: Optional[List[str]] = typer.Option(None, help="Constant definitions in the format 'key=value' (overwrites config file)."), 
    examples: Optional[List[str]] = typer.Option(None, help="Model operators describing desired properties in the final state of the execution (overwrites config file)."), 
    traces_dir: Optional[str] = typer.Option(None, help="Path to store generated trace files (overwrites config file)."),
):
    '''
    Generate execution traces that reach the state described by the `examples` properties.
    '''
    mc_invariants = examples
    if config_path is None and mc_invariants == []:
        print("Error: either --config-path or --desired-states must be specified.")
        raise typer.Exit(code=1)

    # Dict is not supported by typer
    constants = dict([c.split("=") for c in constants])

    config = load_config_file(config_path)
    model_path = config['model_path'] if model_path is None else model_path
    constants = config['constants'] if constants is None else constants
    mc_invariants = config['desired_states'] if mc_invariants is None else mc_invariants
    init = config['init']
    next = config['next']
    traces_dir = config['traces_dir'] if traces_dir is None else traces_dir

    model = _load_model(model_path, init, next, constants)
    if model is None:
        return    
    
    start_time = timer()
    result = model.sample(mc_invariants, constants, traces_dir=traces_dir)
    _print_results(result)
    print(f"Total time: {(timer() - start_time):.2f} seconds")


@app.command()
def info():
    '''
    Display information on the loaded model, if available.
    '''
    global LOG_LEVEL
    model = ModelFile.load(LOG_LEVEL)
    if model is None:
        print("Model file does not exist")
        return

    for k, v in model.info().items():
        print(f"# {k}: {v}")


@app.command()
def reset():
    '''
    Removes any loaded model.
    '''
    if ModelFile.clean():
        print(f'Model file removed')


# @app.command()
# def check_apalache_jar(version = const_values.DEFAULT_APALACHE_VERSION):
#     '''
#     Check whether Apalache's uber jar file is installed, or download it otherwise.
#     '''
#     if apalache_jar.apalache_jar_exists(expected_version=version):
#         print(f'Apalache jar file exists at {const_values.DEFAULT_APALACHE_JAR}')
#         version = apalache_jar.apalache_jar_version()
#         print(f'Apalache jar version: {version}')
#     else:
#         print(f'Apalache jar file not found; will attempt to download it...')
#         apalache_jar.apalache_jar_download(expected_version=version)
#         print(f'Done')

