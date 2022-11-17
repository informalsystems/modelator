import logging
import os
import re
from typing import Dict, Optional

from .. import const_values


def create_logger(logger_name, loglevel):
    logger = logging.getLogger(logger_name)
    numeric_level = getattr(logging, loglevel.upper(), None)
    if not isinstance(numeric_level, int):
        raise ValueError("Invalid log level: %s" % loglevel)
    logger.setLevel(numeric_level)

    # create console handler and set level to debug
    ch = logging.StreamHandler()
    ch.setLevel(logging.DEBUG)

    # create formatter
    formatter = logging.Formatter(
        "%(asctime)s - %(name)s - %(levelname)s - %(message)s", datefmt="%H:%M:%S"
    )

    # add formatter to ch
    ch.setFormatter(formatter)

    # add ch to logger
    # TODO: clarify why adding this line adds double logger
    logger.addHandler(ch)

    return logger


def wrap_command(
    cmd: str,
    tla_file_name: str,
    files: Dict[str, str],
    checker: str = const_values.APALACHE,
    args: Dict = None,
    num_workers: int = 4,
):

    json_command = {}
    json_command["args"] = {}

    # TODO: come up with a more systematic way of setting defaults when they would make more sense for an end user
    # (such as here, where Apalache default for nworkers is 1) --> maybe inside shell, at the very frontend?

    # this is necessary: sending an invalid argument to apalache commands will result
    # in an exception
    if cmd == const_values.CHECK_CMD:
        if checker == const_values.APALACHE:
            json_command["args"]["nworkers"] = num_workers

        else:
            json_command["args"]["workers"] = "auto"

    if cmd == const_values.CHECK_CMD:
        tla_module_name = tla_file_name.split(".")[0]
        config_file_name = tla_module_name + ".cfg"
        if config_file_name in files:
            json_command["args"][const_values.CONFIG] = config_file_name

    if args is not None:
        for arg in args:
            json_command["args"][arg] = args[arg]

    if cmd == const_values.PARSE_CMD:
        not_accepted_args = [
            a
            for a in json_command["args"]
            if a not in const_values.PARSE_CMD_ARGS
            and a not in const_values.GLOBAL_ARGS
        ]
        for e in not_accepted_args:
            json_command["args"].pop(e)

    if cmd == const_values.TYPECHECK_CMD:
        not_accepted_args = [
            a
            for a in json_command["args"]
            if a not in const_values.TYPECHECK_CMD_ARGS
            and a not in const_values.GLOBAL_ARGS
        ]
        for e in not_accepted_args:
            json_command["args"].pop(e)

    json_command["args"]["file"] = os.path.basename(tla_file_name)

    # send only basenames of files to modelator-py
    json_command["files"] = {os.path.basename(f): files[f] for f in files}

    if checker == const_values.TLC:
        json_command["jar"] = os.path.abspath(const_values.DEFAULT_TLC_JAR)
    else:
        json_command["jar"] = os.path.abspath(const_values.DEFAULT_APALACHE_JAR)

    if checker == const_values.APALACHE:
        json_command["args"]["cmd"] = cmd

    return json_command


def extract_line_with(prefix, text) -> Optional[str]:
    """
    Extract from text the line that starts with the given prefix, without
    including the prefix.
    """
    try:
        return re.search(f"^{prefix}(.*)$", text, re.MULTILINE).group(1)
    except AttributeError:
        return None
