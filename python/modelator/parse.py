import argparse
import json
import os
from typing import Tuple
from modelator_py.apalache.pure import apalache_pure
from . import utils

from .constants import DEFAULT_APALACHE_JAR

def parse(
    tla_file_content: str,     
    cfg_file_content: str = None, 
    apalache_jar_path = None
    ) -> Tuple[bool, str]:
    
    json_command = {}
    json_command["args"] = {}
    json_command["args"]["cmd"] = "parse"    

    specName = utils.extract_tla_module_name(tla_file_content) + ".tla"
    json_command["args"]["file"] = specName

    json_command["files"] = {specName: tla_file_content}
    
    if apalache_jar_path is None:
        json_command["jar"] = os.path.abspath(DEFAULT_APALACHE_JAR)
    else:
        json_command["jar"] = apalache_jar_path

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
    
    parse(tla_file_content=tla_file_content)
    
