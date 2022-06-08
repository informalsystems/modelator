import imp
import os
from typing import AnyStr

import pytest

from modelator.Model import Model
from modelator.utils.model_exceptions import ModelParsingError


def test_parse():
    parsable_tests = ["tests/sampleFiles/parse/correct/dir1/Hello_Hi.tla"]
    for t in parsable_tests:
        m = Model.parse_file(file_name=t)
        assert isinstance(m, Model)

    unparsable_tests = [
        "tests/sampleFiles/parse/flawed/dir1/HelloFlawed1.tla",
        "tests/sampleFiles/parse/flawed/dir2/HelloFlawed2.tla",
    ]
    for t in unparsable_tests:
        with pytest.raises(ModelParsingError):
            m = Model.parse_file(file_name=t)
