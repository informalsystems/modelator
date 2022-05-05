import argparse
import os
from typing import Tuple
from modelator_py.apalache.pure import apalache_pure
from . import utils
# import utils

from .constants import DEFAULT_APALACHE_JAR
# from constants import DEFAULT_APALACHE_JAR

"""
The function sends the TLA+ model file (`tla_file_content`) to apalache parse command.
Returns (True, "") if tla_file_content parses, otherwise (False, msg), where msg is a message for why 
the model does not parse.

TODO: cfg_file_content argument is not used. Apalache only has a command for parsing .tla files
and in its new version it does not even load .cfg files by default. Is there a need to parse .cfg files
or shall we take all the common arguments from .cfg and make them command-line arguments?
"""
def parse(
    tla_file_content: str,     
    cfg_file_content: str = None
    ) -> Tuple[bool, str]: 

    if not isinstance(tla_file_content, str):
        raise TypeError("`tla_file_content` should be string")
    
    json_command = {}
    json_command["args"] = {}
    json_command["args"]["cmd"] = "parse"    

    specName = utils.extract_tla_module_name(tla_file_content) + ".tla"
    json_command["args"]["file"] = specName

    json_command["files"] = {specName: tla_file_content}    
    json_command["jar"] = os.path.abspath(DEFAULT_APALACHE_JAR)

    result = apalache_pure(json=json_command)

    if result["return_code"] == 0:
        return (True, "")
    else:
        error = utils.extract_parse_error(result["stdout"])        
        return (False, error)
    

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("model_name")
    parser.add_argument("config_name")
    
    args = parser.parse_args()
    
    
    modelFH = open(args.model_name)
    tla_file_content = modelFH.read()
    
    ret, msg = parse(tla_file_content=tla_file_content)
    
