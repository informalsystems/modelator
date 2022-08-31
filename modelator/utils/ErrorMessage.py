from dataclasses import dataclass
from typing import Optional


@dataclass
class ErrorMessage:
    problem_description: str
    location: Optional[int] = None
    full_error_msg: str = ""
    file_path: str = ""
    error_category: str = ""

    def __str__(self) -> str:
        if self.location:
            locationInfo = ":" + str(self.location)
        else:
            locationInfo = ""

        kind = self.error_category.capitalize()
        location = f"{self.file_path}{locationInfo}"

        s = ""
        if kind:
            s += f"{kind} error"
        if location:
            if not kind:
                s += "error"
            s += f" at {location}"
        if s:
            s += ":\n"
        s += self.problem_description

        return s
