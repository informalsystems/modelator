import os

import pytest

from modelator.Model import Model
from modelator.typecheck import typecheck
from modelator.utils import tla_helpers
from modelator.utils.model_exceptions import ModelTypecheckingError


def test_typecheck():
    well_typed = [
        os.path.abspath("tests/sampleFiles/typecheck/correct/dir1/Hello_Hi.tla")
    ]

    for f in well_typed:
        m = Model.parse_file(file_name=f)
        m.typecheck()

    badly_typed = [
        os.path.abspath("tests/sampleFiles/typecheck/flawed/dir1/Hello1.tla"),
        os.path.abspath("tests/sampleFiles/typecheck/flawed/dir2/Hello2.tla"),
    ]
    for f in badly_typed:
        m = Model.parse_file(file_name=f)
        with pytest.raises(ModelTypecheckingError):
            m.typecheck()
