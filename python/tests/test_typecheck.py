import os
from modelator.typecheck import typecheck
from modelator.utils import tla_helpers


def _matchingTypecheckValue(samples, expectedResult: bool, msgEmpty: bool):
    for test_dir, test_name in samples.items():
        files = tla_helpers.get_auxiliary_tla_files(os.path.join(test_dir, test_name))        

        res, msg = typecheck(files=files, tla_file_name=test_name)
        assert res == expectedResult
        if msgEmpty is True:
            assert msg.problem_description == ""
        else:
            assert len(msg.problem_description) > 0


def test_typecheck():
    well_typed = {
        os.path.abspath("tests/sampleFiles/typecheck/correct/dir1"): "Hello_Hi.tla"
        }    
    _matchingTypecheckValue(well_typed, True, True)

    badly_typed = {
        os.path.abspath("tests/sampleFiles/parse/flawed/dir1"):"HelloFlawed1.tla",
        os.path.abspath("tests/sampleFiles/parse/flawed/dir2"): "HelloFlawed2"
    }
    _matchingTypecheckValue(badly_typed, False, False)
