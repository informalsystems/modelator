import os
import re
from .constants import DEFAULT_APALACHE_JAR

def extract_tla_module_name(tla_file_content: str):
    match = re.search("-+[ ]*MODULE[ ]*(?P<moduleName>\w+)[ ]*-+", tla_file_content)
    if match is None:
        return None
    return match.group('moduleName')


def extract_parse_error(parser_output: str):
    report = []
    reportActive = False
    for line in parser_output.splitlines():
    
        if line == "Residual stack trace follows:":
            break

        if reportActive is True:
            report.append(line)

        if line == "***Parse Error***":
            reportActive = True
                
    if len(report) == 0:
        return None
    else:
        return "\n".join(report)        


def wrap_apalache_command(cmd, tla_file_content, args=None):
    json_command = {}
    json_command["args"] = {}
    json_command["args"]["cmd"] = "parse"    

    specName = extract_tla_module_name(tla_file_content) + ".tla"
    json_command["args"]["file"] = specName

    json_command["files"] = {specName: tla_file_content}    
    json_command["jar"] = os.path.abspath(DEFAULT_APALACHE_JAR)
    return json_command