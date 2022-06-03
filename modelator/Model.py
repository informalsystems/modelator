import argparse
import os
from typing import Any, Dict, List, Optional, Union
from typing_extensions import Self
from modelator.ModelMonitor import ModelMonitor
from modelator.ModelResult import ModelResult
from modelator.utils.model_exceptions import (
    ModelError,
    ModelParsingError,
    ModelTypecheckingError,
    ModelCheckingError,
)
from modelator.utils import tla_helpers
from modelator.parse import parse
from modelator.typecheck import typecheck
from modelator.utils.shell_helpers import shell
from modelator import constants
from modelator.check import check_apalache, check_tlc


class Model:
    @classmethod
    @shell
    def parse_file(
        cls, file_name: str, init: str = "Init", next: str = "Next"
    ) -> Union[Self, ModelParsingError]:

        # invoke callback functions for all existing monitors

        auxiliary_files = tla_helpers.get_auxiliary_tla_files(file_name)

        # TODO: how to handle .cfg files? They are actually necessary for TLC

        m = Model(
            tla_file_path=file_name,
            init_predicate=init,
            next_predicate=next,
            files_contents=auxiliary_files,
        )
        # a member function which will raise a ModelParsingError exception in case of problems
        m._parse()

        return m

    def _parse(self) -> Optional[ModelParsingError]:
        # a helper function: if the file is not parsable
        for monitor in self.monitors:
            monitor.on_parse_start(res=ModelResult(model=self))
        try:
            parse(tla_file_name=self.tla_file_path, files=self.files_contents)
            self.parsable = True
        except ModelParsingError as p_error:
            self.parsable = False
            raise p_error
        else:
            # TODO: this only works when the model is in a single file (it will not get all the
            # operators from all extendees)
            (
                self.variables,
                self.operators,
                self.module_name,
            ) = tla_helpers.get_model_elements(self.tla_file_path)

            # TODO: add this part once we have support for models defined in multiple files
            # if not (self.init_predicate in self.operators and self.next_predicate in self.operators):
            #     raise ValueError("Predicates {} and {} have to be defined".format(self.init_predicate, self.next_predicate))

        finally:
            for monitor in self.monitors:
                monitor.on_parse_finish(res=ModelResult(self))

    @shell
    def typecheck(self) -> Optional[ModelTypecheckingError]:

        # a helper function which will raise a ModelTypechecking exception in case types do not match
        typecheck(tla_file_name=self.tla_file_path, files=self.files_contents)

    def instantiate(self, model_constants: Dict):
        self.model_constants = model_constants

    def sample(
        self,
        examples: List[str] = None,
        model_constants: Dict = None,
        checker: str = constants.APALACHE,
        checker_params: Dict = None,
    ) -> ModelResult:

        sampling_constants = self.model_constants
        if model_constants is not None:
            sampling_constants.update(model_constants)

        if examples is not None:
            example_predicates = examples
        else:
            # take all operators that are prefixed/suffixed with Ex
            example_predicates = [
                str(op)
                for op in self.operators
                if tla_helpers._default_example_criteria(str(op))
            ]

        mod_res = ModelResult(model=self, all_operators=example_predicates)

        for monitor in self.monitors:
            monitor.on_sample_start(res=mod_res)

        for example_predicate in example_predicates:
            # TODO: this whole block should probably be moved to a separate function
            # TODO: this needs to be rewritten as a separate process for each call

            (
                negated_name,
                negated_content,
                negated_predicates,
            ) = tla_helpers.tla_file_with_negated_predicates(
                module_name=self.module_name, predicates=[example_predicate]
            )

            self.files_contents[negated_name] = negated_content

            args_config_file = tla_helpers._basic_args_to_config_string(
                init=self.init_predicate,
                next=self.next_predicate,
                invariants=negated_predicates,
                constants_names=sampling_constants,
            )

            args_config_file_name = "generated_config.cfg"
            args = {constants.CONFIG: args_config_file_name}
            self.files_contents[args_config_file_name] = args_config_file

            if checker_params is None:
                checker_params = {}

            if checker == constants.TLC:
                args.update(checker_params)
                try:
                    res, msg, cex = check_tlc(
                        tla_file_name=negated_name,
                        files=self.files_contents,
                        args=args,
                    )
                except Exception as e:
                    print("Problem running TLC: {}".format(e))
                    raise ModelCheckingError(e)

            else:  # if checker is Apalache

                args.update(tla_helpers._set_additional_apalache_args())
                try:
                    res, msg, cex = check_apalache(
                        negated_name,
                        self.files_contents,
                        args=args,
                    )
                except Exception as e:
                    print("Problem runing Apalache: {}".format(e))
                    raise ModelCheckingError(e)

            mod_res._finished_operators.append(example_predicate)
            mod_res._in_progress_operators.remove(example_predicate)
            if res is True:
                mod_res._unsuccessful.append(example_predicate)
            else:
                mod_res._successful.append(example_predicate)

                # in the current implementation, this will only return one trace (as a counterexample)
                mod_res._traces[example_predicate] = cex

            for monitor in self.monitors:
                monitor.on_sample_update(res=mod_res)

        for monitor in self.monitors:
            monitor.on_sample_finish(res=mod_res)

        return mod_res

    def __init__(
        self,
        tla_file_path: str,
        init_predicate: str,
        next_predicate: str,
        files_contents: Dict[str, str] = None,
        constants: Dict[str, Any] = None,
    ) -> None:

        # an entry file for the tla model
        self.tla_file_path = tla_file_path
        # init and next predicates, which are obligatory for all models
        self.init_predicate = init_predicate
        self.next_predicate = next_predicate

        # a dictionary file_name --> file_content, for relevant filenames
        self.files_contents = files_contents if files_contents is not None else {}

        # a dcitionary of constant values relevant to the model
        self.model_constants = constants if constants is not None else {}

        # a list of results for all checks performed on this model
        self.all_checks = []

        # a list of results for all samples performed on this model
        self.all_samples = []

        # a list of monitors which track the progress of model actions
        self.monitors: List[ModelMonitor] = []

    def add_monitor(self, monitor: ModelMonitor):
        self.monitors.append(monitor)

    def remove_monitor(self, monitor: ModelMonitor):
        self.monitors.remove(monitor)
