import argparse

from typing import Tuple
from modelator_py.apalache.pure import apalache_pure
from . import utils
# import utils



"""
The function sends the TLA+ model file (`tla_file_content`) to apalache Snowcat typechecker.
Returns (True, "") if tla_file_content Typechecks, otherwise (False, msg), where msg is a message for why 
the model does not typecheck.
"""
def typecheck(tla_file_content: str) -> Tuple[bool, str]: 

    if not isinstance(tla_file_content, str):
        raise TypeError("`tla_file_content` should be string")
    
    json_command = utils.wrap_apalache_command(cmd="typecheck", tla_file_content=tla_file_content)

    result = apalache_pure(json=json_command)

    if result["return_code"] == 0:
        return (True, "")
    else:
        error = utils.extract_typecheck_error(result["stdout"])        
        return (False, error)
    



if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("model_name")    
    
    args = parser.parse_args()
    
    
    modelFH = open(args.model_name)
    tla_file_content = modelFH.read()
    
    ret, msg = typecheck(tla_file_content=tla_file_content)    
    print(msg)
