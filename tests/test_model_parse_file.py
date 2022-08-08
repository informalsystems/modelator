import pytest

from modelator.Model import Model
from modelator.utils.model_exceptions import ModelParsingError


def test_parse_file_success():
    file_path = "tests/sampleFiles/parse/correct/dir1/Hello_Hi.tla"
    m = Model.parse_file(file_path)
    assert isinstance(m, Model)

def test_parse_file_fail_indentation():
    file_path = "tests/sampleFiles/parse/flawed/dir1/HelloFlawed1.tla"
    with pytest.raises(ModelParsingError):
        Model.parse_file(file_path)

def test_parse_file_fail_extra_comma():
    file_path = "tests/sampleFiles/parse/flawed/dir2/HelloFlawed2.tla"
    with pytest.raises(ModelParsingError):
        Model.parse_file(file_path)
