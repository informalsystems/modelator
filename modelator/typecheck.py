import os
from typing import Dict

from modelator_py.apalache.pure import apalache_pure

from modelator import const_values
from modelator.utils.apalache_helpers import extract_typecheck_error
from modelator.utils.model_exceptions import ModelTypecheckingError
from modelator.utils.modelator_helpers import wrap_command


def typecheck(tla_file_name: str, files: Dict[str, str], args: Dict[str, str]):
    """
    Call Apalache's typechecker. Return nothing if ok, otherwise raise a
    ModelParsingError.
    """
    json_command = wrap_command(
        const_values.TYPECHECK_CMD, tla_file_name, files, args=args
    )
    result = apalache_pure(json=json_command)

    if result["return_code"] != 0:
        try:
            error, error_file, line_number = extract_typecheck_error(result["stdout"])
        except Exception as e:
            error = f"Unknown error:\n{e}"
            error_file = None
            line_number = None

        if error_file:
            files_dir = os.path.dirname(tla_file_name)
            error_file_name = os.path.join(files_dir, error_file)
        else:
            error_file_name = tla_file_name

        raise ModelTypecheckingError(
            problem_description=error,
            location=line_number,
            full_error_msg=result["stdout"],
            file_path=os.path.abspath(error_file_name),
        )
