import os
from typing import AnyStr

import pytest
from modelator.parse import parse


def _matchingParseValue(samplesDirectory, expectedResult: bool, msgEmpty: bool):
    for filename in os.listdir(samplesDirectory):
        f = os.path.join(samplesDirectory, filename)
        tla_file_content = open(f).read()
        res, msg = parse(tla_file_content=tla_file_content)
        assert res == expectedResult
        if msgEmpty is True:
            assert msg == ""
        else:
            assert len(msg) > 0


def test_parse():
    correctSamples = os.path.abspath("tests/sampleFiles/parse/correct")
    _matchingParseValue(correctSamples, True, True)

    flawedSamples = os.path.abspath("tests/sampleFiles/parse/flawed")    
    _matchingParseValue(flawedSamples, False, False)


def test_parse_test_args():

    # the case when an argument of a wrong type is given as tla_file_content
    with pytest.raises(TypeError):
        _, _ = parse(tla_file_content=[2])