import json
import os
import re
from typing import Dict
from ..constants import DEFAULT_APALACHE_JAR

def extract_tla_module_name(tla_file_content: str):
    match = re.search(r"-+[ ]*MODULE[ ]*(?P<moduleName>\w+)[ ]*-+", tla_file_content)
    if match is None:
        return None
    return match.group('moduleName')

def extract_apalache_counterexample(apalache_result: Dict):
    cex_tla = apalache_result["files"]["counterexample.tla"]
    msg = ""    
    for line in cex_tla.splitlines():
        invMark = "InvariantViolation == "
        if invMark in line:
            inv = line[len(invMark):].strip()
    
    msg = "Invariant violated: {}".format(inv)
    cex_itf = json.loads(apalache_result["files"]["counterexample.itf.json"])
    cex = cex_itf["states"]

    return (msg, cex)

def extract_parse_error(parser_output: str):
    report = []
    reportActive = False
    line_number = None
    for line in parser_output.splitlines():
    
        if line == "Residual stack trace follows:":
            break

        if reportActive is True:
            report.append(line)
            match = re.search(r"at line (?P<lineNumber>\d+)", line)
            if match is not None:
                line_number = int(match.group('lineNumber'))


        if line == "***Parse Error***":
            reportActive = True
                
    if len(report) == 0:
        return (None, None)
    else:        
        return ("\n".join(report), line_number)


def extract_typecheck_error(parser_output: str):
    report = []
    reportActive = False
    line_number = None
    for line in parser_output.splitlines():
        
        if reportActive is True and ("Snowcat asks you to fix the types" in line or "It took me" in line):
            break

        if reportActive is True:
            match = re.search("\[\w+\.tla:(?P<lineNumber>\d+):.+\]: (?P<info>.+) E@.+", line)
            if match is not None:
                info = match["info"]
                if line_number is None:
                    line_number = match["lineNumber"]
                
            report.append(info)
        if "Running Snowcat" in line:
            reportActive = True       

    if len(report) == 0:
        return None, None
    else:
        return ("\n".join(report), line_number)


def wrap_apalache_command(
    cmd:str, 
    tla_file_content:str, 
    cfg_file_content: str = None,
    args: Dict = None,
    num_workers: int = 4
    ):


    json_command = {}
    json_command["args"] = {}
    json_command["args"]["cmd"] = cmd
    
    #TODO: come up with a more systematic way of setting defaults when they would make more sense for an end user
    # (such as here, where Apalache default for nworkers is 1) --> maybe inside shell, at the very frontend?

    # this is necessary: sending an invalid argument to apalache commands will result
    # in an exception
    if cmd == "check":
        json_command["args"]["nworkers"] = num_workers

    tla_module_name = extract_tla_module_name(tla_file_content)
    spec_name = tla_module_name  + ".tla"
    json_command["args"]["file"] = spec_name

    json_command["files"] = {spec_name: tla_file_content}   

    if cfg_file_content is not None:
        config_name = tla_module_name + ".cfg"
        json_command["args"]["config"] = config_name
        json_command["files"][config_name] = cfg_file_content

    if args is not None:
        for arg in args:
            json_command["args"][arg] = args[arg]

    json_command["jar"] = os.path.abspath(DEFAULT_APALACHE_JAR)
    return json_command