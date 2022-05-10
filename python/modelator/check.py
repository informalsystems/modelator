
import argparse
from typing import Tuple, List

from modelator_py.apalache.pure import apalache_pure
from . import utils
from .parse import parse
from .typecheck import typecheck
from typing import Dict

def check_apalache(
    tla_file_content: str, 
    cfg_file_content: str = None,
    apalache_args: Dict = {},
    do_parse: bool = True,
    do_typecheck: bool = True) -> Tuple[bool, str, List]:

    if not isinstance(tla_file_content, str):
        raise TypeError("`tla_file_content` should be a string")

    if cfg_file_content is not None and not isinstance(cfg_file_content, str):
        raise TypeError("`cfg_file_content` should be a string")
    
    if do_parse is True:
        parsable, msg = parse(tla_file_content)
        if parsable is False:
            return (False, msg, [])
        
    
    if do_typecheck is True:
        good_types, msg = typecheck(tla_file_content)
        if good_types is False:
            return (False, msg, [])

    json_command = utils.wrap_apalache_command(
        cmd="check", 
        tla_file_content=tla_file_content, 
        cfg_file_content=cfg_file_content,
        args=apalache_args
        )

    result = apalache_pure(json=json_command)
    
    if result["return_code"] == 0:
        return (True, "", [])
    else:
        error, cex = utils.extract_apalache_counterexample(result)        
        return (False, error, cex)

    


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("model_name")    
    parser.add_argument("config_name")    
    
    args = parser.parse_args()
    
    
    modelFH = open(args.model_name)
    tla_file_content = modelFH.read()

    configFH = open(args.config_name)
    config_file_content = configFH.read()
        
    ret, msg, cex = check_apalache(tla_file_content=tla_file_content, cfg_file_content=config_file_content)
    print("message is: {}".format(msg))
