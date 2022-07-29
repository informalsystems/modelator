import glob

import pytest

from modelator.itf import ITF


@pytest.mark.parametrize("itf_json_file", glob.glob("tests/traces/itf/*.itf.json"))
def test_itf_parse_and_diff(snapshot, itf_json_file):
    trace = ITF.from_itf_json(itf_json_file)
    diff = ITF.diff(trace)
    assert (trace, diff) == snapshot


@pytest.mark.parametrize("itf_json_file", glob.glob("tests/traces/itf/*.itf.json"))
def test_itf_diff_print(capfd, snapshot, itf_json_file):
    trace = ITF.from_itf_json(itf_json_file)
    ITF.print_diff(trace)
    out, _ = capfd.readouterr()
    assert out == snapshot
