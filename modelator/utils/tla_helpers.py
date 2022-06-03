import os
from typing import Dict, List, Tuple
import tla as tla_parsing


def get_auxiliary_tla_files(model_name: str) -> Dict[str, str]:

    dir = os.path.dirname(os.path.abspath(model_name))
    tla_files = [
        os.path.join(dir, f)
        for f in os.listdir(dir)
        if os.path.isfile(os.path.join(dir, f)) and f.split(".")[-1] in ["tla", "cfg"]
    ]

    files = {}
    for file_name in tla_files:
        files[file_name] = open(file_name).read()

    return files


def get_model_elements(model_name: str) -> Tuple[List[str], List[str]]:
    """
    TODO: this only works when the model is in a single file (it will not get all the
        operators from all extendees)

    """

    with open(model_name, "r") as f:
        tla_spec = f.read()
        tree = tla_parsing.parser.parse(tla_spec)
        variables = []
        operators = []
        if tree is None:
            raise ValueError("Expecting this file to be parsable")
        else:
            for body_element in tree.body:
                if isinstance(body_element, tla_parsing.ast.Nodes.Variables):
                    variables = [str(d) for d in body_element.declarations]

                if isinstance(body_element, tla_parsing.ast.Nodes.Definition):
                    operators.append(body_element.definition.name)

        return variables, operators


def create_file(module, extends, content):
    return f"""
------------ MODULE {module} -------------

EXTENDS {", ".join(extends)}

{content}

===========================================
    """
