import hashlib
import os
from typing import Dict
from .. import const_values
import logging
import subprocess
from urllib.request import urlopen
import zipfile
import io


def check_for_apalache_jar(
    download_location=const_values.DEFAULT_APALACHE_LOCATION,
    jar_path=const_values.DEFAULT_APALACHE_JAR,
    expected_version=const_values.DEFAULT_APALACHE_VERSION,
    sha256_checksum=None,
) -> bool:

    """
    Checks for existence of the Apalache jar, version `expected_version`.
    If it is missing, downloads it to `download_location` and returns False.
    If it is already there, does nothing and returns True.

    It is meant to be used with default arguments.
    The reason that arguments exist is to enable testing.
    """

    if sha256_checksum is None:
        try:
            sha256_checksum = const_values.APALACHE_SHA_CHECKSUMS[expected_version]
        except KeyError:
            raise ValueError(
                "SHA Checksum is missing. Provide it either as an argument to\
             `modelator_helpers.check_for_apalache_jar`, or add it to `const_values.APALACHE_SHA_CHECKSUMS`"
            )

    apalache_release_url = "https://github.com/informalsystems/apalache/releases/download/v{}/apalache.zip".format(
        expected_version
    )

    logging.debug("checking for jar at {}".format(jar_path))
    try:
        download_needed = False
        version = subprocess.check_output(
            ["java", "-jar", jar_path, "version"], text=True, stderr=subprocess.STDOUT
        ).strip()
        logging.debug(
            "Currently existing version is {} and we are looking for {}".format(
                version, expected_version
            )
        )
        if not version == expected_version:
            download_needed = True
    except subprocess.CalledProcessError:
        logging.debug("Error checking version of the jar")
        download_needed = True
    finally:
        if download_needed is True:
            with urlopen(apalache_release_url) as zip_response:
                data = zip_response.read()

                assert sha256_checksum == hashlib.sha256(data).hexdigest()
                with zipfile.ZipFile(io.BytesIO(data)) as zip_file:
                    zip_file.extract(
                        member="apalache/lib/apalache.jar", path=download_location
                    )
                    logging.debug(
                        "Downloaded version {} to location {}".format(
                            expected_version, download_location
                        )
                    )

        return download_needed


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

    if args is not None and cmd != const_values.CHECK_CMD:
        assert "config" not in args

    if checker == const_values.APALACHE:
        json_command["args"]["cmd"] = cmd

    # TODO: come up with a more systematic way of setting defaults when they would make more sense for an end user
    # (such as here, where Apalache default for nworkers is 1) --> maybe inside shell, at the very frontend?

    # this is necessary: sending an invalid argument to apalache commands will result
    # in an exception
    if cmd == const_values.CHECK_CMD:
        if checker == const_values.APALACHE:
            json_command["args"]["nworkers"] = num_workers

        else:
            json_command["args"]["workers"] = "auto"

    json_command["args"]["file"] = os.path.basename(tla_file_name)

    # send only basenames of files to modelator-py
    json_command["files"] = {os.path.basename(f): files[f] for f in files}

    if cmd == const_values.CHECK_CMD:
        tla_module_name = tla_file_name.split(".")[0]
        config_file_name = tla_module_name + ".cfg"
        if config_file_name in files:
            json_command["args"]["config"] = config_file_name

    if args is not None:
        for arg in args:
            json_command["args"][arg] = args[arg]

    if checker == const_values.TLC:
        json_command["jar"] = os.path.abspath(const_values.DEFAULT_TLC_JAR)
    else:
        json_command["jar"] = os.path.abspath(const_values.DEFAULT_APALACHE_JAR)

    return json_command
