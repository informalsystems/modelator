import os
from typing import Dict
from modelator.check import check_apalache
from modelator.utils import tla_helpers


def _matching_check_value(
    test_dir: str,
    tla_file_name: str,
    expected_result: bool,
    msg_is_empty: bool,
    config_file_name: str = None,
    args: Dict = None,
    check_function=check_apalache,
):
    files = tla_helpers.get_auxiliary_tla_files(os.path.join(test_dir, tla_file_name))

    res, msg, cex = check_function(
        files=files,
        tla_file_name=tla_file_name,
        config_file_name=config_file_name,
        args=args,
    )
    assert res == expected_result

    if msg_is_empty:
        assert msg.problem_description == ""
    else:
        assert len(msg.problem_description) > 0


def test_check_apalache_invariant_holds():
    _matching_check_value(
        test_dir=os.path.abspath("tests/sampleFiles/check/correct/dir1"),
        tla_file_name="Hello.tla",
        config_file_name="Hello.cfg",
        expected_result=True,
        msg_is_empty=True,
        check_function=check_apalache,
    )

def test_check_apalache_invariant_does_not_hold():
    _matching_check_value(
        test_dir=os.path.abspath("tests/sampleFiles/check/flawed/dir1"),
        tla_file_name="Hello.tla",
        config_file_name="Hello.cfg",
        expected_result=False,
        msg_is_empty=False,
        check_function=check_apalache,
    )
