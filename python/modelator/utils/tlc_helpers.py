import re


def invariant_from_stdout(stdout: str) -> str:
    match = re.search(r"Invariant (?P<invName>\w+) is violated.", stdout)
    return match["invName"]
