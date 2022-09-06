import glob

import pytest
from pyrsistent import pmap, pset, pvector

from modelator.itf import ITF
from modelator.pytest.decorators import sanitize_itf


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


sanitize_pairs = [
    (
        {
            "#meta": 1,
            "#info": "test",
            "states": [
                {
                    "keys": "list",
                    "func": {"#map": [(["1", "2"], ["1and2"])]},
                    "set": {"#set": [(["1", "2"], ["2", "3"])]},
                },
                {
                    "keys": "set",
                    "func": {"#map": [({"#set": ["1", "2"]}, ["1and2"])]},
                    "set": {"#map": [({"#set": ["1", "2"]}, {"#set": ["2", "3"]})]},
                },
                {
                    "keys": "map",
                    "func": {"#map": [({"#map": [("1", "2")]}, ["1and2"])]},
                    "set": {"#map": [({"#map": [("1", "2")]}, {"#map": [("2", "3")]})]},
                },
            ],
        },
        {
            "states": [
                {
                    "func": {pvector(["1", "2"]): ["1and2"]},
                    "keys": "list",
                    "set": {(pvector(["1", "2"]), pvector(["2", "3"]))},
                },
                {
                    "func": {pset(["2", "1"]): ["1and2"]},
                    "keys": "set",
                    "set": {pset(["2", "1"]): {"2", "3"}},
                },
                {
                    "func": {pmap({"1": "2"}): ["1and2"]},
                    "keys": "map",
                    "set": {pmap({"1": "2"}): {"2": "3"}},
                },
            ],
        },
    ),
    (
        {
            "states": [
                {
                    "var_bigint": {"#bigint": "1000000000000000000000000000001"},
                    "var_tuple": {"#tup": ["1", "2", "3"]},
                }
            ]
        },
        {
            "states": [
                {
                    "var_bigint": 1000000000000000000000000000001,
                    "var_tuple": pvector(["1", "2", "3"]),
                }
            ]
        },
    ),
]


@pytest.mark.parametrize("a,b", sanitize_pairs)
def test_sanitize_itf(a, b):
    assert sanitize_itf(a) == b
