import os
from typing import Dict, Optional

from typing import Tuple
from modelator_py.apalache.pure import apalache_pure

from . import const_values
from .utils import apalache_helpers, modelator_helpers, tla_helpers
from .utils.model_exceptions import ModelParsingError


# import utils


"""
The function sends the TLA+ model file (`tla_file_content`) to apalache parse command.
Returns (True, "") if tla_file_content parses, otherwise (False, msg), where msg is a message for why
the model does not parse.
"""


def parse(tla_file_name: str, files: Dict[str, str]) -> Optional[ModelParsingError]:

    json_command = modelator_helpers.wrap_command(
        cmd="parse", tla_file_name=tla_file_name, files=files
    )

    result = apalache_pure(json=json_command)

    if not result["return_code"] == 0:
        (
            error_description,
            file_name,
            line_number,
        ) = apalache_helpers.extract_parse_error(result["stdout"])
        files_dir = os.path.dirname(tla_file_name)
        raise ModelParsingError(
            problem_description=error_description,
            location=line_number,
            full_error_msg=result["stdout"],
            file_path=os.path.abspath(os.path.join(files_dir, file_name)),
        )
