from operator import neg
import os
from typing import Dict, List, Tuple
import modelator_py.util.tla as tla_parsing
from modelator import const_values


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


def _basic_args_to_config_string(
    init: str, next: str, invariants: List[str], constants_names: List[str]
):
    conf_string: str = "INIT {}\nNEXT {}\nINVARIANTS {}".format(
        init, next, "  \n".join(invariants)
    )
    if len(constants_names) > 0:
        conf_string = conf_string + "\nCONSTANTS {}".format(" \n".join(const_values))
    return conf_string


def _set_additional_apalache_args():
    apalache_args = {}
    apalache_args[const_values.APALACHE_NUM_STEPS] = 1000
    return apalache_args


def _negated_predicate(predicate_name: str):
    return predicate_name + "_negated"


def _clear_negation_from_predicate(predicate_name: str):
    assert predicate_name.endswith("_negated")
    return predicate_name[: -len("_negated")]


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
