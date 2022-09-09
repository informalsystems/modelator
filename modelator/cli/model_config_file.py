from pathlib import Path

import toml


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
    config["params"] = config["Apalache"]
    del config["Apalache"]

    config = _flatten(config)

    return config


def _supported_apalache_parameters():
    return [
        # the name of an operator that initializes CONSTANTS, default: None
        "cinit",
        # configuration file in TLC format
        "config",
        # maximal number of Next steps; default: 10
        "length",
        # do not stop on first error, but produce up to a given number of counterexamples (fine tune with --view), default: 1
        "max_error",
        # do not check for deadlocks; default: false
        "no_deadlock",
        # save an example trace for each simulated run, default: false
        # not supported by modelator-py
        # "save_runs",
        # the state view to use with --max-error=n, default: transition index
        "view",
    ]


def _set_default_values(config):
    """
    Set default values for missing keys in the configuration.
    """
    config = {"Model": {}, "Constants": {}, "Config": {}, "Apalache": {}, **config}

    config["Model"] = {
        "init": "Init",
        "next": "Next",
        "invariants": [],
        "tests": [],
        "config_file_path": None,
        **config["Model"],
    }

    config["Config"] = {
        "traces_dir": None,
        **config["Config"],
    }

    default_apalache_params = {p: None for p in _supported_apalache_parameters()}
    config["Apalache"] = {**default_apalache_params, **config["Apalache"]}

    return config


def _flatten(config):
    """
    Flatten nested dictionaries.
    """
    config = {**config, **config["Model"]}
    del config["Model"]

    config["constants"] = config["Constants"]
    del config["Constants"]

    config = {**config, **config["Config"]}
    del config["Config"]

    return config
