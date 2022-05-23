from dataclasses import dataclass


@dataclass
class ErrorMessage:
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
