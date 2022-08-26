import json
import os
import re
from pathlib import Path
from typing import Dict, List

from modelator.const_values import APALACHE_DEFAULTS


def extract_tla_module_name(tla_file_content: str):
    match = re.search(r"-+[ ]*MODULE[ ]*(?P<moduleName>\w+)[ ]*-+", tla_file_content)
    if match is None:
        return None
    return match.group("moduleName")


def write_trace_files_to(apalache_result: Dict, traces_dir: str) -> List[str]:
    # create directory if it does not exist
    Path(traces_dir).mkdir(parents=True, exist_ok=True)

    itfs_filenames = [
        f for f in apalache_result["files"].keys() if f.endswith(".itf.json")
    ]
    itfs_filenames.sort()

    trace_paths = []
    for filename in itfs_filenames:

        path = os.path.join(traces_dir, filename)

        if Path(path).is_file():
            print(f"WARNING: existing file will be overwritten: {path}")

        with open(path, "w+") as f:
            f.write(apalache_result["files"][filename])
            trace_paths.append(path)

    return trace_paths


def extract_apalache_counterexample(apalache_result: Dict):
    cex_tla = apalache_result["files"][APALACHE_DEFAULTS["result_violation_tla_file"]]
    msg = ""
    for line in cex_tla.splitlines():
        invMark = "InvariantViolation == "
        if invMark in line:
            msg = line[len(invMark) :].strip()
            break

    cex_itf = json.loads(
        apalache_result["files"][APALACHE_DEFAULTS["result_violation_itf_file"]]
    )
    cex = cex_itf["states"]

    return (msg, cex)


def extract_parse_error(parser_output: str):
    report = []
    reportActive = False
    line_number = None
    file_name = None
    for line in parser_output.splitlines():
        # this will trigger for every parsed file, but the last update will be before the error happens
        if line.startswith("Parsing file "):
            # taking only the file name, because apalache runs in a temporary directory,
            # so all the info about absolute paths is useless
            file_name = line[len("Parsing file ") :].split("/")[-1]
        if line == "Residual stack trace follows:":
            break

        if reportActive is True:
            report.append(line)
            match = re.search(r"at line (?P<lineNumber>\d+)", line)
            if match is not None:
                line_number = int(match.group("lineNumber"))

        if line == "***Parse Error***":
            reportActive = True

    if len(report) == 0:
        return (None, None, None)
    else:
        return ("\n".join(report), file_name, line_number)


def extract_typecheck_error(parser_output: str):
    report = []
    reportActive = False
    line_number = None
    file_name = None
    for line in parser_output.splitlines():

        if reportActive is True and (
            "Snowcat asks you to fix the types" in line or "It took me" in line
        ):
            break

        if reportActive is True:
            # find error reports which point to exact locations
            match_exact_loc = re.search(
                "\[(?P<fileName>\w+\.tla):(?P<lineNumber>\d+):.+\]: (?P<info>.+) E@.+",
                line,
            )
            if match_exact_loc is not None:
                info = match_exact_loc["info"]
                file_name = match_exact_loc["fileName"]
                if line_number is None:
                    line_number = match_exact_loc["lineNumber"]

            else:
                match_general_typing_error = re.search(
                    "Typing input error:(?P<info>.+) E@.+", line
                )
                info = match_general_typing_error["info"].strip()
                line_number = ""

            report.append(info)
        if "Running Snowcat" in line:
            reportActive = True

    if len(report) == 0:
        return None, None, None
    else:
        return ("\n".join(report), file_name, line_number)
