import os
import pytest
from modelator.Model import Model
from modelator.utils.model_exceptions import ModelTypecheckingError


def test_typecheck_success():
    file_path = "tests/sampleFiles/typecheck/correct/dir1/Hello_Hi.tla"
    m = Model.parse_file(os.path.abspath(file_path))
    m.typecheck()


def test_typecheck_fail_wrong_type_annotation():
    file_path = "tests/sampleFiles/typecheck/flawed/dir1/Hello1.tla"
    m = Model.parse_file(os.path.abspath(file_path))
    with pytest.raises(ModelTypecheckingError):
        m.typecheck()


def test_typecheck_fail_missing_type_annotation():
    file_path = "tests/sampleFiles/typecheck/flawed/dir2/Hello2.tla"
    m = Model.parse_file(os.path.abspath(file_path))
    with pytest.raises(ModelTypecheckingError):
        m.typecheck()
