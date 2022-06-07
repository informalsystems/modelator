from dataclasses import dataclass
from .. import const_values


@dataclass
class ModelError(Exception):
    problem_description: str
    location: int = None
    full_error_msg: str = ""
    file_path: str = ""
    error_category: str = ""

    def __str__(self) -> str:
        if self.location is not None:
            locationInfo = ":" + str(self.location)
        else:
            locationInfo = ""
        error_message = "{kind} error at {path}{lineNum}:\n{errorContent}".format(
            kind=self.error_category.capitalize(),
            path=self.file_path,
            lineNum=locationInfo,
            errorContent=self.problem_description,
        )

        return error_message


class ModelCheckingError(ModelError):
    def __init__(self, exc):
        raise exc


class ModelParsingError(ModelError):
    def __init__(self, problem_description, location, full_error_msg, file_path):
        super().__init__(
            problem_description,
            location,
            full_error_msg,
            file_path,
            error_category=const_values.PARSE,
        )


class ModelTypecheckingError(ModelError):
    def __init__(self, problem_description, location, full_error_msg, file_path):
        super().__init__(
            problem_description,
            location,
            full_error_msg,
            file_path,
            error_category=const_values.TYPECHECK,
        )
