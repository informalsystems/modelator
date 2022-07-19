# model checkers
import os
import appdirs


APALACHE = "apalache"
TLC = "tlc"

DEFAULT_APALACHE_VERSION = "0.25.0"
DEFAULT_APALACHE_LOCATION = os.path.join(appdirs.user_data_dir(__package__), "checkers")
DEFAULT_APALACHE_JAR = os.path.join(
    DEFAULT_APALACHE_LOCATION, "apalache", "lib", "apalache.jar"
)
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
