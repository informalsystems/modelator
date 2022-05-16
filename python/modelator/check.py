import argparse
import json
import os
from typing import Tuple, List

from modelator_py.apalache.pure import apalache_pure
from .utils import apalache_helpers, tla_helpers
from .parse import parse
from .typecheck import typecheck
from typing import Dict
from .utils.ErrorMessage import ErrorMessage
from . import constants


def check_apalache(
    tla_file_name: str,
    files: Dict[str, str],
    apalache_args: Dict = None,
    do_parse: bool = True,
    do_typecheck: bool = True,
    config_file_name: str = None,
) -> Tuple[bool, ErrorMessage, List]:

    if do_parse is True:
        parsable, msg = parse(tla_file_name=tla_file_name, files=files)
        if parsable is False:
            return (False, msg, [])

    if do_typecheck is True:
        good_types, msg = typecheck(tla_file_name=tla_file_name, files=files)
        if good_types is False:
            return (False, msg, [])

    if config_file_name is not None:
        if apalache_args is None:
            apalache_args = {}

        apalache_args["config"] = config_file_name

    json_command = apalache_helpers.wrap_apalache_command(
        cmd=constants.APALACHE_CHECK,
        tla_file_name=tla_file_name,
        files=files,
        args=apalache_args,
    )

    result = apalache_pure(json=json_command)

    if result["return_code"] == 0:
        return (True, ErrorMessage(""), [])
    else:
        inv_violated, cex = apalache_helpers.extract_apalache_counterexample(result)
        cex_representation = str(cex)
        problem_desc = "Invariant {} violated.\nCounterexample is {}".format(
            inv_violated, cex_representation
        )
        error_msg = ErrorMessage(
            problem_description=problem_desc,
            error_category=constants.CHECK,
            full_error_msg=result["stdout"],
        )
        return (False, error_msg, cex)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("model_file")

    parser.add_argument("--invariant", default="Inv")
    parser.add_argument("--init", default="Init")
    parser.add_argument("--next", default="Next")
    parser.add_argument("--config", default=None)

    args = parser.parse_args()

    if args.config is None:
        apalache_args = {
            constants.INIT: args.init,
            constants.NEXT: args.next,
            constants.INVARIANT: args.invariant,
        }
    else:
        apalache_args = None
    files = tla_helpers.get_auxiliary_tla_files(os.path.abspath(args.model_file))
    model_name = os.path.basename(args.model_file)

    ret, msg, cex = check_apalache(
        tla_file_name=model_name,
        files=files,
        apalache_args=apalache_args,
        config_file_name=args.config,
    )
    if ret is True:
        print("Invariant holds")
    else:
        print(msg)
