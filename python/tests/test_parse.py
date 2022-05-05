import os

import pytest
from modelator.parse import parse

def test_parse():
    samplesDirectory = os.path.abspath("tests/sampleFiles")

    for filename in os.listdir(samplesDirectory):
        f = os.path.join(samplesDirectory, filename)
        tla_file_content = open(f).read()
        res, _ = parse(tla_file_content=tla_file_content)
        if "Flawed" in filename:
            assert res is False
        else:
            assert res is True

def test_parse_test_args():

    # the case when an argument of a wrong type is given as tla_file_content
    with pytest.raises(TypeError):
        _, _ = parse(tla_file_content=[2])