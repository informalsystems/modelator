import argparse
import os

from typing import Dict, Tuple
from modelator_py.apalache.pure import apalache_pure
from .utils import apalache_helpers, modelator_helpers, tla_helpers
from .utils.ErrorMessage import ErrorMessage
from modelator.utils.model_exceptions import ModelError, ModelTypecheckingError
from .parse import parse
from . import const_values

# import utils


"""
The function sends the TLA+ model file (`tla_file_content`) to apalache Snowcat typechecker.
Returns (True, "") if tla_file_content Typechecks, otherwise (False, msg), where msg is a message for why
the model does not typecheck.
"""


def typecheck(
    tla_file_name: str, files: Dict[str, str], do_parse: bool = True
) -> ModelError:

    # commenting out for now. If there really is a way to make sure the model can
    # always be up to date and parsed upon a change, this is not neccessary
    # if do_parse is True:
    #     parse(tla_file_name=tla_file_name, files=files)

    json_command = modelator_helpers.wrap_command(
        cmd=const_values.TYPECHECK_CMD, tla_file_name=tla_file_name, files=files
    )

    result = apalache_pure(json=json_command)

    if not result["return_code"] == 0:
        (
            error,
            extracted_file_name,
            line_number,
        ) = apalache_helpers.extract_typecheck_error(result["stdout"])
        if extracted_file_name is not None:
            files_dir = os.path.dirname(tla_file_name)
            error_file_name = os.path.join(files_dir, extracted_file_name)
        else:
            error_file_name = tla_file_name
        raise ModelTypecheckingError(
            problem_description=error,
            location=line_number,
            full_error_msg=result["stdout"],
            file_path=os.path.abspath(error_file_name),
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("model_file")

    args = parser.parse_args()

    files = tla_helpers.get_auxiliary_tla_files(os.path.abspath(args.model_file))
    model_name = os.path.basename(args.model_file)

    ret, msg = typecheck(tla_file_name=model_name, files=files)
