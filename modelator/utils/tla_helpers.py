import os
from typing import Dict, List, Tuple

import modelator_py.util.tla as tla_parsing


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


def _default_example_criteria(operator_name: str):
    op = operator_name.lower()
    return op.startswith("ex") or op.endswith("ex") or op.endswith("example")


def _default_invariant_criteria(operator_name: str):
    op = operator_name.lower()
    return op.startswith("inv") or op.endswith("inv") or op.endswith("invariant")


def build_config_file_content(
    init: str, next: str, invariants: List[str], constants: Dict[str, str]
):
    invariants_string = "  \n".join(invariants)
    config_string = f"INIT {init}\nNEXT {next}\nINVARIANTS {invariants_string}"
    if constants:
        constants_string = "  \n".join([f"{k} <- {v}" for k, v in constants.items()])
        config_string += f"\nCONSTANTS {constants_string}"

    return config_string


def _negated_predicate(predicate_name: str):
    return predicate_name + "_negated"


def tla_file_with_negated_predicates(
    module_name: str, predicates: List[str]
) -> Tuple[str, str, str]:
    negated_module_name = module_name + "__negated"
    negated_file_name = negated_module_name + ".tla"
    negated_predicates = []
    header = "------------ MODULE {} -------------\n EXTENDS {}\n".format(
        negated_module_name, module_name
    )
    body = []
    for predicate in predicates:

        neg_predicate = _negated_predicate(predicate)
        negated_predicates.append(neg_predicate)
        body.append("{} == ~{}".format(neg_predicate, predicate))
    footer = "===="
    negated_file_content = header + "\n".join(body) + "\n" + footer

    return negated_file_name, negated_file_content, negated_predicates


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

        return variables, operators, tree.name


def create_file(module, extends, content):
    return f"""
------------ MODULE {module} -------------

EXTENDS {", ".join(extends)}

{content}

===========================================
    """
