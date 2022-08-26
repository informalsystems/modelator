import argparse
import os
from typing import Dict, Optional

from modelator_py.apalache.pure import apalache_pure
from modelator_py.tlc.pure import tlc_pure
from modelator_py.util.tlc import tlc_itf

from modelator.checker.CheckResult import CheckResult
from modelator.const_values import APALACHE_STDOUT
from modelator import const_values
from modelator.utils import (
    apalache_helpers,
    tla_helpers,
    tlc_helpers,
)
from modelator.utils.modelator_helpers import (
    create_logger,
    extract_line_with,
    wrap_command,
)

from ..itf import ITF
from ..parse import parse
from ..typecheck import typecheck
from ..utils.ErrorMessage import ErrorMessage

check_logger = create_logger(logger_name=__file__, loglevel="debug")


def check_tlc(
    tla_file_name: str,
    files: Dict[str, str],
    args: Dict = {},
    do_parse: bool = True,
    config_file_name: str = None,
    traces_dir: Optional[str] = None,
) -> CheckResult:

    if do_parse is True:
        parse(tla_file_name=tla_file_name, files=files)

    if config_file_name is not None:
        args["config"] = config_file_name

    json_command = wrap_command(
        cmd=const_values.CHECK_CMD,
        checker=const_values.TLC,
        tla_file_name=tla_file_name,
        files=files,
        args=args,
    )

    result = tlc_pure(json=json_command)
    if result["return_code"] == 0:
        return CheckResult(True)

    itf_trace_objects = tlc_itf(
        json={"stdout": result["stdout"], "lists": True, "records": True}
    )

    counterexample = itf_trace_objects[0]["states"]
    inv_violated = tlc_helpers.invariant_from_stdout(result["stdout"])

    trace = [ITF(state) for state in counterexample]
    error_msg = ErrorMessage(
        problem_description=f"Invariant {inv_violated} violated.\nCounterexample is {trace}",
        error_category=const_values.CHECK,
        full_error_msg=result["stdout"],
    )
    return CheckResult(False, error_msg, trace)


def check_apalache(
    tla_file_name: str,
    files: Dict[str, str],
    args: Dict = {},
    do_parse: bool = True,
    do_typecheck: bool = True,
    config_file_name: Optional[str] = None,
    traces_dir: Optional[str] = None,
) -> CheckResult:

    if do_parse is True:
        parse(tla_file_name, files)

    if do_typecheck is True:
        typecheck(tla_file_name, files)

    if config_file_name is not None:
        args["config"] = config_file_name

    json_command = wrap_command(
        cmd=const_values.CHECK_CMD,
        tla_file_name=tla_file_name,
        files=files,
        args=args,
    )
    check_logger.debug(f"command jar: {json_command['jar']}")
    check_logger.debug(f"command args: {json_command['args']}")
    check_logger.debug(f"command files: {json_command['files'].keys()}")
    if "generated_config.cfg" in json_command["files"]:
        check_logger.debug(
            f"command config: {json_command['files']['generated_config.cfg']}"
        )

    result = apalache_pure(json=json_command)
    check_logger.debug(f"result return_code: {result['return_code']}")
    check_logger.debug(f"result shell_cmd: {result['shell_cmd']}")
    check_logger.debug(f"result files: {result['files'].keys()}")
    check_logger.debug(f"result stdout: {result['stdout']}")

    if traces_dir:
        trace_paths = apalache_helpers.write_trace_files_to(result, traces_dir)
        for trace_path in trace_paths:
            check_logger.info(f"Wrote trace file to {trace_path}")
    else:
        trace_paths = []

    if result["return_code"] == 0:
        return CheckResult(True, trace_paths=trace_paths)

    if APALACHE_STDOUT["CONSTANTS_NOT_INITIALIZED"] in result["stdout"]:
        return CheckResult(
            False, ErrorMessage("A constant in the model is not initialized")
        )

    config_error = extract_line_with(APALACHE_STDOUT["CONFIG_ERROR"], result["stdout"])
    if config_error:
        return CheckResult(
            False, ErrorMessage(config_error, error_category="Configuration")
        )

    try:
        inv_violated, counterexample = apalache_helpers.extract_counterexample(
            result["files"]
        )
    except:
        check_logger.error(
            f"Could not extract counterexample from Apalache output: {result['stdout']}"
        )
        raise

    trace = [ITF(state) for state in counterexample]
    error_msg = ErrorMessage(
        problem_description=f"Invariant {inv_violated} violated.\nCounterexample is {trace}",
        error_category=const_values.CHECK,
        full_error_msg=result["stdout"],
    )
    return CheckResult(False, error_msg, trace, trace_paths)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("model_file")

    parser.add_argument("--checker", default=const_values.APALACHE)
    parser.add_argument("--invariant", default="Inv")
    parser.add_argument("--init", default="Init")
    parser.add_argument("--next", default="Next")
    parser.add_argument("--config", default=None)

    args = parser.parse_args()

    apalache_args = {}
    if args.config is None:
        apalache_args = {
            const_values.INIT: args.init,
            const_values.NEXT: args.next,
            const_values.INVARIANT: args.invariant,
        }

    files = tla_helpers.get_auxiliary_tla_files(os.path.abspath(args.model_file))
    model_name = os.path.basename(args.model_file)

    if args.checker == const_values.APALACHE:
        check_result = check_apalache(
            tla_file_name=model_name,
            files=files,
            args=apalache_args,
            config_file_name=args.config,
        )
    else:
        check_result = check_tlc(
            tla_file_name=model_name,
            files=files,
            config_file_name=args.config,
        )
