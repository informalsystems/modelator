import argparse
import os
from typing import Tuple, List

from modelator_py.apalache.pure import apalache_pure
from modelator_py.tlc.pure import tlc_pure
from modelator_py.util.tlc import tlc_itf

from .utils import apalache_helpers, tla_helpers, modelatorpy_helpers, tlc_helpers
from .parse import parse
from .typecheck import typecheck
from typing import Dict
from .utils.ErrorMessage import ErrorMessage
from . import constants
from .itf import ITF

import re


def check_tlc(
    tla_file_name: str,
    files: Dict[str, str],
    args: Dict = None,
    do_parse: bool = True,
    config_file_name: str = None,
) -> Tuple[bool, ErrorMessage, List]:

    if do_parse is True:
        parse(tla_file_name=tla_file_name, files=files)

    if config_file_name is not None:
        if args is None:
            args = {}
        args["config"] = config_file_name

    json_command = modelatorpy_helpers.wrap_command(
        cmd=constants.CHECK_CMD,
        checker=constants.TLC,
        tla_file_name=tla_file_name,
        files=files,
        args=args,
    )

    result = tlc_pure(json=json_command)
    if result["return_code"] == 0:
        return (True, ErrorMessage(""), [])
    else:
        tlc_itf_json = {"stdout": result["stdout"], "lists": True, "records": True}
        itf_trace_objects = tlc_itf(json=tlc_itf_json)

        cex = itf_trace_objects[0]["states"]
        inv_violated = tlc_helpers.invariant_from_stdout(result["stdout"])

        cex_representation = [ITF(state) for state in cex]
        problem_desc = "Invariant {} violated.\nCounterexample is {}".format(
            inv_violated, cex_representation
        )
        error_msg = ErrorMessage(
            problem_description=problem_desc,
            error_category=constants.CHECK,
            full_error_msg=result["stdout"],
        )
        return (False, error_msg, cex_representation)


def check_apalache(
    tla_file_name: str,
    files: Dict[str, str],
    args: Dict = None,
    do_parse: bool = True,
    do_typecheck: bool = True,
    config_file_name: str = None,
) -> Tuple[bool, ErrorMessage, List]:

    if do_parse is True:
        parse(tla_file_name=tla_file_name, files=files)

    if do_typecheck is True:
        typecheck(tla_file_name=tla_file_name, files=files)

    if config_file_name is not None:
        if args is None:
            args = {}

        args["config"] = config_file_name

    json_command = modelatorpy_helpers.wrap_command(
        cmd=constants.CHECK_CMD,
        tla_file_name=tla_file_name,
        files=files,
        args=args,
    )

    result = apalache_pure(json=json_command)

    if result["return_code"] == 0:
        return (True, ErrorMessage(""), [])
    else:
        inv_violated, cex = apalache_helpers.extract_apalache_counterexample(result)
        cex_representation = [ITF(state) for state in cex]
        problem_desc = "Invariant {} violated.\nCounterexample is {}".format(
            inv_violated, cex_representation
        )
        error_msg = ErrorMessage(
            problem_description=problem_desc,
            error_category=constants.CHECK,
            full_error_msg=result["stdout"],
        )
        return (False, error_msg, cex_representation)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("model_file")

    parser.add_argument("--checker", default=constants.APALACHE)
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

    if args.checker == constants.APALACHE:
        ret, msg, cex = check_apalache(
            tla_file_name=model_name,
            files=files,
            args=apalache_args,
            config_file_name=args.config,
        )
    else:
        ret, msg, cex = check_tlc(
            tla_file_name=model_name,
            files=files,
            config_file_name=args.config,
        )
    if ret is True:
        print("Invariant holds")
    else:
        print(msg)
