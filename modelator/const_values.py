# model checkers
import os

import appdirs

APALACHE = "apalache"
TLC = "tlc"

DEFAULT_APALACHE_VERSION = "0.30.1"
DEFAULT_CHECKERS_LOCATION = os.path.join(appdirs.user_data_dir(__package__), "checkers")
DEFAULT_APALACHE_LOCATION = os.path.join(DEFAULT_CHECKERS_LOCATION, "apalache")

DEFAULT_APALACHE_JAR_FILENAME = f"apalache-{DEFAULT_APALACHE_VERSION}.jar"
DEFAULT_APALACHE_JAR = os.path.join(
    DEFAULT_APALACHE_LOCATION,
    "lib",
    DEFAULT_APALACHE_JAR_FILENAME,
)
APALACHE_SHA_CHECKSUMS = {
    "0.25.0": "41a60d1e2d5ab0f4d523b5821f61e0907d03b00f4d22edb997779722a08800f7",
    "0.25.1": "1746f04311e36dfce4289f12ba8fc0a314e1e56ecf83b461e3f1b18114eea5c6",
    "0.25.10": "1844511c579891b413377dde18a1d6ac30304a5859d4c3631a8ef02313a2e08d",
}

APALACHE_DEFAULTS = {
    "result_violation_tla_file": "violation.tla",
    "result_violation_itf_file": "violation.itf.json",
    "trace_name": "violation",
}

APALACHE_STDOUT = {
    "CONSTANTS_NOT_INITIALIZED": "CONSTANTS are not initialized",
    "CONFIG_ERROR": "Configuration error",
    "INVARIANT_VIOLATION": "InvariantViolation == ",
}


def apalache_release_url(expected_version):
    return f"https://github.com/informalsystems/apalache/releases/download/v{expected_version}/apalache.zip"


def apalache_checksum_url(expected_version: str):
    return f"https://github.com/informalsystems/apalache/releases/download/v{expected_version}/sha256sum.txt"


DEFAULT_TLC_JAR = "jars/tla2tools-v1.8.0.jar"

PARSE = "parse"
TYPECHECK = "typecheck"
CHECK = "check"

PARSE_CMD = "parse"
CHECK_CMD = "check"
TYPECHECK_CMD = "typecheck"
SIMULATE_CMD = "simulate"

GLOBAL_ARGS = ["features", "out_dir"]

PARSE_CMD_ARGS = ["output"]
TYPECHECK_CMD_ARGS = ["infer_poly", "output"]

DEFAULT_INVARIANTS = ["Inv"]
DEFAULT_INIT = "Init"
DEFAULT_NEXT = "Next"
DEFAULT_TRACES_DIR = "./traces/"

INIT = "init"
NEXT = "next"
INVARIANT = "inv"
APALACHE_NUM_STEPS = "length"
CONFIG = "config"

SHELL_ACTIVE = False


CHECKER_TIMEOUT = 60
