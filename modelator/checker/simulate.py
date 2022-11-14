from typing import Dict, Optional

from modelator_py.apalache.pure import apalache_pure

from modelator import const_values
from modelator.utils import apalache_helpers
from modelator.utils.modelator_helpers import create_logger, wrap_command

from ..itf import ITF
from ..parse import parse
from ..typecheck import typecheck

simulate_logger = create_logger(logger_name=__file__, loglevel="error")


def simulate_apalache(
    tla_file_name: str,
    files: Dict[str, str],
    args: Dict = {},
    do_parse: bool = True,
    do_typecheck: bool = True,
    traces_dir: Optional[str] = None,
    cmd=const_values.SIMULATE_CMD,
):
    simulate_logger.debug("# SIMULATE_apalache")
    simulate_logger.debug(f"- tla_file_name: {tla_file_name}")
    simulate_logger.debug(f"- files: {list(files.keys())}")
    simulate_logger.debug(f"- args: {args}")
    simulate_logger.debug(f"- traces_dir: {traces_dir}")

    if do_parse is True:
        parse(tla_file_name, files, args)

    if do_typecheck is True:
        typecheck(tla_file_name, files, args)

    json_command = wrap_command(
        cmd=cmd,
        tla_file_name=tla_file_name,
        files=files,
        args=args,
    )
    simulate_logger.debug(f"command jar: {json_command['jar']}")
    simulate_logger.debug(f"command args: {json_command['args']}")
    simulate_logger.debug(f"command files: {list(json_command['files'].keys())}")
    if json_command["args"][const_values.CONFIG] in json_command["files"]:
        simulate_logger.debug(
            f"command config: {json_command['files'][json_command['args'][const_values.CONFIG]]}"
        )

    result = apalache_pure(json=json_command)
    simulate_logger.debug(f"result return_code: {result['return_code']}")
    simulate_logger.debug(f"result shell_cmd: {result['shell_cmd']}")
    simulate_logger.debug(f"result files: {list(result['files'].keys())}")
    simulate_logger.debug(f"result stdout: {result['stdout']}")

    traces_paths = []
    if traces_dir:
        trace_paths = apalache_helpers.write_trace_files_to(
            result, traces_dir, simulate=True
        )
        for trace_path in trace_paths:
            simulate_logger.info(f"Wrote trace file to {trace_path}")
            traces_paths.append(trace_path)

    simulation_tests = apalache_helpers.extract_simulations(trace_paths=trace_paths)
    traces = [[ITF(state) for state in trace] for trace in simulation_tests]
    return traces, traces_paths
