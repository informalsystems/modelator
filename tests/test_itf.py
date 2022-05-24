import glob
import pytest

from modelator.itf import ITF


@pytest.mark.parametrize("itf_json_file", glob.glob("tests/traces/itf/*.itf.json"))
def test_itf_parse(snapshot, itf_json_file):
    trace = ITF.from_itf_json(itf_json_file)
    diff = ITF.diff(trace)
    assert (trace, diff) == snapshot
