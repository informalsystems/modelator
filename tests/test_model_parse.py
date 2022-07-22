import os
import pytest
from modelator.Model import Model
from modelator.utils.model_exceptions import ModelParsingError


def test_parse_success():
    file_path = "tests/sampleFiles/parse/correct/dir1/Hello_Hi.tla"
    files_contents = {
        os.path.basename(file_path): open(file_path).read()
    }
    m = Model(file_path, "Init", "Next", files_contents)
    m._parse()
    assert isinstance(m, Model)

def test_parse_fail_indentation():
    file_path = "tests/sampleFiles/parse/flawed/dir1/HelloFlawed1.tla"
    files_contents = {
        os.path.basename(file_path): open(file_path).read()
    }
    m = Model(file_path, "Init", "Next", files_contents)
    with pytest.raises(ModelParsingError):
        m._parse()

def test_parse_fail_extra_comma():
    file_path = "tests/sampleFiles/parse/flawed/dir2/HelloFlawed2.tla"
    files_contents = {
        os.path.basename(file_path): open(file_path).read()
    }
    m = Model(file_path, "Init", "Next", files_contents)
    with pytest.raises(ModelParsingError):
        m._parse()
