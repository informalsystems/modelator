import os
from typing import Dict
from modelator.check import check_apalache
from modelator.utils import tla_helpers


def _matchingCheckValue(
    samples, 
    expectedResult: bool, 
    msgEmpty: bool, 
    config_file_name: str = None,
    apalache_args: Dict = None):

    for test_dir, test_name in samples.items():
        files = tla_helpers.get_auxiliary_tla_files(os.path.join(test_dir, test_name))        
        
        res, msg, cex = check_apalache(files=files, tla_file_name=test_name, config_file_name=config_file_name, apalache_args=apalache_args)
        assert res == expectedResult
        if msgEmpty is True:
            assert msg.problem_description == ""
        else:
            assert len(msg.problem_description) > 0


    
    
def test_check():
    args = {}
    args["init"] = "Init"
    args["next"] = "Next"
    args["inv"] = "Inv"

    invariant_holds = {
        os.path.abspath("tests/sampleFiles/check/correct/dir1"): "Hello.tla"
        }    
    config_name = "Hello.cfg"
    _matchingCheckValue(invariant_holds, True, True, config_file_name=config_name)
    # _matchingCheckValue(invariant_holds, True, True, apalache_args=args)

    # args["init"] = "InitA"
    # _matchingCheckValue(invariant_holds, True, True, apalache_args=args)

    # args["init"] = "InitB"
    # _matchingCheckValue(invariant_holds, True, True, apalache_args=args)



    invariant_does_not_hold = {
        os.path.abspath("tests/sampleFiles/check/flawed/dir1"): "Hello.tla"
        }    
    config_name = "Hello.cfg"
    _matchingCheckValue(invariant_does_not_hold, False, False, config_file_name=config_name)


