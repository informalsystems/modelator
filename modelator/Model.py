import argparse
import os
from typing import Any, Dict, List, Optional, Union
from typing_extensions import Self
from modelator.ModelMonitor import ModelMonitor
from modelator.ModelResult import ModelResult
from modelator.utils.model_exceptions import ModelParsingError, ModelTypecheckingError
from modelator.utils import tla_helpers
from modelator.parse import parse
from modelator.typecheck import typecheck
from modelator.utils.shell_helpers import shell


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
            self.variables, self.operators = tla_helpers.get_model_elements(
                self.tla_file_path
            )

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
        self.constants = constants if constants is not None else {}

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
