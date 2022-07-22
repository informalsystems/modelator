import json
import os
from typing import Dict
from modelator_py.apalache.pure import apalache_pure

from .utils import apalache_helpers, modelator_helpers
from .utils.model_exceptions import ModelError, ModelParsingError


def parse(tla_file_path: str, files: Dict[str, str]):
    """
    Parse the TLA+ model in `tla_file_path` with Apalache. If it fails, raise an
    exception.
    """

    json_command = modelator_helpers.wrap_command("parse", tla_file_path, files)
    result = apalache_pure(json=json_command)

    if result["return_code"] != 0:
        (
            error_description,
            file_name,
            line_number,
        ) = apalache_helpers.extract_parse_error(result["stdout"])
        if file_name is None:
            print("parse command: " + json.dumps(json_command, sort_keys=True, indent=4))
            print("Apalache output:\n" + result["stdout"])
            raise ModelError("Could not extract parsing error from Apalache output")

        files_dir = os.path.dirname(tla_file_path)

        raise ModelParsingError(
            problem_description=error_description,
            location=line_number,
            full_error_msg=result["stdout"],
            file_path=os.path.abspath(os.path.join(files_dir, file_name)),
        )
