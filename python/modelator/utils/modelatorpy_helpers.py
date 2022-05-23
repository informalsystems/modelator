import os
from typing import Dict
from .. import constants


def wrap_command(
    cmd: str,
    tla_file_name: str,
    files: Dict[str, str],
    checker: str = constants.APALACHE,
    args: Dict = None,
    num_workers: int = 4,
):

    json_command = {}
    json_command["args"] = {}

    if args is not None and cmd != constants.CHECK_CMD:
        assert "config" not in args

    if checker == constants.APALACHE:
        json_command["args"]["cmd"] = cmd

    # TODO: come up with a more systematic way of setting defaults when they would make more sense for an end user
    # (such as here, where Apalache default for nworkers is 1) --> maybe inside shell, at the very frontend?

    # this is necessary: sending an invalid argument to apalache commands will result
    # in an exception
    if cmd == constants.CHECK_CMD:
        if checker == constants.APALACHE:
            json_command["args"]["nworkers"] = num_workers

        else:
            json_command["args"]["workers"] = "auto"

    json_command["args"]["file"] = tla_file_name

    json_command["files"] = files

    if cmd == constants.CHECK_CMD:
        tla_module_name = tla_file_name.split(".")[0]
        config_file_name = tla_module_name + ".cfg"
        if config_file_name in files:
            json_command["args"]["config"] = config_file_name

    if args is not None:
        for arg in args:
            json_command["args"][arg] = args[arg]

    if checker == constants.TLC:
        json_command["jar"] = os.path.abspath(constants.DEFAULT_TLC_JAR)
    else:
        json_command["jar"] = os.path.abspath(constants.DEFAULT_APALACHE_JAR)

    return json_command
