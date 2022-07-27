from pathlib import Path
import toml


def load_config_file(config_path):
    '''
    Load model and model checker configuration from `config_path`, or return a
    configuration with default values.
    '''
    if config_path:
        if not Path(config_path).is_file():
            raise FileNotFoundError("Config file not found.")

        try:
            config = toml.load(config_path)
        except Exception as e:
            print(f'Error while parsing toml file: {e}')
            raise e

    else:
        config = {}

    # set default values for missing keys
    config = {
        'Model': {}, 'Constants': {}, 'Config': {}
        } | config
    config['Model'] = {
        'model_path': None, 
        'init': 'Init', 'next': 'Next', 
        'invariants': [], 'desired_states': [], 
        'config_file_path': None
        } | config['Model']
    config['Config'] = {
        'check_deadlock': False, 
        'length': 100,
        'traces_dir': None,
        } | config['Config']
    
    config = config | config['Model']
    del config['Model']

    config['constants'] = config['Constants']
    del config['Constants']

    config = config | config['Config']
    del config['Config']

    return config
