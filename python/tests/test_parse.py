import imp
import os
from typing import AnyStr

import pytest
from modelator.parse import parse
from modelator.utils import tla_helpers


def _matchingParseValue(samples, expectedResult: bool, msgEmpty: bool):
    for test_dir, test_name in samples.items():
        files = tla_helpers.get_auxiliary_tla_files(os.path.join(test_dir, test_name))        

        res, msg = parse(files=files, tla_file_name=test_name)
        assert res == expectedResult
        if msgEmpty is True:
            assert msg.problem_description == ""
        else:
            assert len(msg.problem_description) > 0


def test_parse():
    parsable_tests = {
        os.path.abspath("tests/sampleFiles/parse/correct/dir1"): "Hello_Hi.tla"
        }    
    _matchingParseValue(parsable_tests, True, True)

    unparsable_tests = {
        os.path.abspath("tests/sampleFiles/parse/flawed/dir1"):"HelloFlawed1.tla",
        os.path.abspath("tests/sampleFiles/parse/flawed/dir2"): "HelloFlawed2"
    }
    _matchingParseValue(unparsable_tests, False, False)
