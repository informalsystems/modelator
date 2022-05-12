import argparse
import os
from typing import Dict

from typing import Tuple
from modelator_py.apalache.pure import apalache_pure

from . import constants
from .utils import apalache_helpers, tla_helpers
from .utils.ErrorMessage import ErrorMessage
# import utils



"""
The function sends the TLA+ model file (`tla_file_content`) to apalache parse command.
Returns (True, "") if tla_file_content parses, otherwise (False, msg), where msg is a message for why 
the model does not parse.
"""
def parse(tla_file_name: str, files: Dict[str, str]) -> Tuple[bool, ErrorMessage]: 
    
    json_command = apalache_helpers.wrap_apalache_command(
        cmd="parse", 
        tla_file_name=tla_file_name,
        files=files)

    result = apalache_pure(json=json_command)

    if result["return_code"] == 0:
        return (True, ErrorMessage(""))
    else:
        error_description, line_number = apalache_helpers.extract_parse_error(result["stdout"])        
        return (False, ErrorMessage(
            problem_description=error_description, 
            location=line_number,
            error_category=constants.PARSE,
            full_error_msg=result["stdout"]))
    


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("model_file")


    args = parser.parse_args()
    
    files = tla_helpers.get_auxiliary_tla_files(os.path.abspath(args.model_file))  
    model_name = os.path.basename(args.model_file)
        
    ret, msg = parse(tla_file_name=model_name, files=files)
    if ret is True:
        print("successful parse")
    else:
        print(msg)
