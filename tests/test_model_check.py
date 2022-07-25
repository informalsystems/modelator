import os
from typing import Dict
from modelator.checker.check import check_apalache, check_tlc
from modelator.utils import tla_helpers


def _matching_check_value(
    test_dir: str,
    tla_file_name: str,
    expected_result: bool,
    config_file_name: str = None,
    args: Dict = {},
    check_function=check_apalache,
):
    files = tla_helpers.get_auxiliary_tla_files(os.path.join(test_dir, tla_file_name))

    check_result = check_function(
        files=files,
        tla_file_name=tla_file_name,
        config_file_name=config_file_name,
        args=args,
    )
    print(check_result)

    assert check_result.is_ok == expected_result
    assert (check_result.error_msg is None) == check_result.is_ok


def test_check_apalache_invariant_holds():
    _matching_check_value(
        test_dir=os.path.abspath("tests/sampleFiles/check/correct/dir1"),
        tla_file_name="Hello.tla",
        config_file_name="Hello.cfg",
        expected_result=True,
        check_function=check_apalache,
    )


def test_check_apalache_invariant_does_not_hold():
    _matching_check_value(
        test_dir=os.path.abspath("tests/sampleFiles/check/flawed/dir1"),
        tla_file_name="Hello.tla",
        config_file_name="Hello.cfg",
        expected_result=False,
        check_function=check_apalache,
    )


# def test_check_tlc_invariant_holds():
#     _matching_check_value(
#         test_dir=os.path.abspath("tests/sampleFiles/check/correct/dir1"),
#         tla_file_name="Hello.tla",
#         config_file_name="Hello.cfg",
#         expected_result=True,
#         check_function=check_tlc,
#     )
