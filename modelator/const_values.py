# model checkers
import os
import appdirs


APALACHE = "apalache"
TLC = "tlc"

DEFAULT_APALACHE_VERSION = "0.25.0"
APALACHE_SHA256 = "41a60d1e2d5ab0f4d523b5821f61e0907d03b00f4d22edb997779722a08800f7"
DEFAULT_APALACHE_LOCATION = os.path.join(appdirs.user_data_dir(__package__), "checkers")
DEFAULT_APALACHE_JAR = os.path.join(
    DEFAULT_APALACHE_LOCATION, "apalache", "lib", "apalache.jar"
)
APALACHE_SHA_CHECKSUMS = {
    "0.25.0": "41a60d1e2d5ab0f4d523b5821f61e0907d03b00f4d22edb997779722a08800f7",
    "0.25.1": "1746f04311e36dfce4289f12ba8fc0a314e1e56ecf83b461e3f1b18114eea5c6",
}

DEFAULT_TLC_JAR = "jars/tla2tools-v1.8.0.jar"

PARSE = "parse"
TYPECHECK = "typecheck"
CHECK = "check"

PARSE_CMD = "parse"
CHECK_CMD = "check"
TYPECHECK_CMD = "typecheck"

DEFAULT_INVARIANTS = ["Inv"]
DEFAULT_INIT = "Init"
DEFAULT_NEXT = "Next"

INIT = "init"
NEXT = "next"
INVARIANT = "inv"
APALACHE_NUM_STEPS = "length"
CONFIG = "config"

SHELL_ACTIVE = False


CHECKER_TIMEOUT = 60
