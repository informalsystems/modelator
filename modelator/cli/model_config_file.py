from pathlib import Path

import toml


def _model_checker_params():
    """
    List of model-checker parameters that we support.
    """
    return [
        "cinit",
        "config",
        "no_deadlock",
        "length",
        "max_error",
        "save_runs",
        "view",
    ]


def _set_default_values(config):
    """
    Set default values for missing keys in the configuration.
    """
    config = {"Model": {}, "Constants": {}, "Config": {}, "Checker": {}} | config

    config["Model"] = {
        "model_path": None,
        "init": "Init",
        "next": "Next",
        "invariants": [],
        "examples": [],
        "config_file_path": None,
    } | config["Model"]

    config["Config"] = {
        "traces_dir": None,
    } | config["Config"]

    default_params = dict([(p, None) for p in _model_checker_params()])
    config["Checker"] = default_params | config["Checker"]

    return config


def _flatten(config):
    """
    Flatten nested dictionaries.
    """
    config = config | config["Model"]
    del config["Model"]

    config["constants"] = config["Constants"]
    del config["Constants"]

    config = config | config["Config"]
    del config["Config"]

    return config


def load_config_file(config_path):
    """
    Load model and model checker configuration from `config_path`, or return a
    configuration with default values.
    """
    config = {}
    if config_path:
        if not Path(config_path).is_file():
            raise FileNotFoundError("Config file not found.")

        try:
            config = toml.load(config_path)
        except Exception as e:
            print(f"Error while parsing toml file: {e}")
            raise e

    config = _set_default_values(config)

    # use the same key name as in the CLI commands
    config["params"] = config["Checker"]
    del config["Checker"]

    config = _flatten(config)

    return config
