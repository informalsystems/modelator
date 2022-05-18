import argparse
import os

from typing import Dict, Tuple
from modelator_py.apalache.pure import apalache_pure
from .utils import apalache_helpers, tla_helpers, modelatorpy_helpers
from .utils.ErrorMessage import ErrorMessage
from .parse import parse
from . import constants

# import utils


"""
The function sends the TLA+ model file (`tla_file_content`) to apalache Snowcat typechecker.
Returns (True, "") if tla_file_content Typechecks, otherwise (False, msg), where msg is a message for why
the model does not typecheck.
"""


def typecheck(
    tla_file_name: str, files: Dict[str, str], do_parse: bool = True
) -> Tuple[bool, ErrorMessage]:

    if do_parse is True:
        res, msg = parse(tla_file_name=tla_file_name, files=files)
        if res is False:
            return (False, msg)

    json_command = modelatorpy_helpers.wrap_command(
        cmd=constants.TYPECHECK_CMD, tla_file_name=tla_file_name, files=files
    )

    result = apalache_pure(json=json_command)

    if result["return_code"] == 0:
        return (True, ErrorMessage(""))
    else:
        error, line_number = apalache_helpers.extract_typecheck_error(result["stdout"])
        return (
            False,
            ErrorMessage(
                problem_description=error,
                location=line_number,
                full_error_msg=result["stdout"],
                error_category=constants.TYPECHECK,
            ),
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("model_file")

    args = parser.parse_args()

    files = tla_helpers.get_auxiliary_tla_files(os.path.abspath(args.model_file))
    model_name = os.path.basename(args.model_file)

    ret, msg = typecheck(tla_file_name=model_name, files=files)
    if ret is True:
        print("successful typechecking")
    else:
        print(msg)
