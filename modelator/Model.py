import logging
import threading
from copy import copy
from typing import Any, Dict, List, Optional, Union

from typing_extensions import Self

from modelator import const_values
from modelator.checker.check import check_apalache, check_tlc
from modelator.ModelMonitor import ModelMonitor
from modelator.ModelResult import ModelResult
from modelator.parse import parse
from modelator.typecheck import typecheck
from modelator.utils import modelator_helpers, tla_helpers
from modelator.utils.model_exceptions import (
    ModelCheckingError,
    ModelParsingError,
    ModelTypecheckingError,
)


class Model:
    @classmethod
    def parse_file(
        cls, file_name: str, init: str = "Init", next: str = "Next"
    ) -> Union[Self, ModelParsingError]:

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

        for monitor in self.monitors:
            monitor.on_parse_start(res=ModelResult(model=self))
        try:
            parse(tla_file_name=self.tla_file_path, files=self.files_contents)
            self.parsable = True
        except ModelParsingError as p_error:
            self.parsable = False
            self.last_parsing_error = p_error
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
                monitor.on_parse_finish(
                    res=ModelResult(self, parsing_error=not self.parsable)
                )

    def typecheck(self) -> Optional[ModelTypecheckingError]:
        if self.parsable is False:
            raise self.last_parsing_error

        parsing_not_needed = self.parsable is True and self.autoparse is True
        # a helper function which will raise a ModelTypechecking exception in case types do not match
        typecheck(
            tla_file_name=self.tla_file_path,
            files=self.files_contents,
            do_parse=not parsing_not_needed,
        )

    def instantiate(self, constants: Dict):
        self.constants = constants

    def _modelcheck_predicates(
        self,
        predicates,
        constants,
        checker,
        tla_file_name,
        checking_files_content,
        checker_params,
        traces_dir,
    ):
        args_config_file = tla_helpers._basic_args_to_config_string(
            init=self.init_predicate,
            next=self.next_predicate,
            invariants=predicates,
            constants_names=constants,
        )

        args_config_file_name = "generated_config.cfg"

        args = {const_values.CONFIG: args_config_file_name} | checker_params
        checking_files_content.update({args_config_file_name: args_config_file})

        if checker == const_values.TLC:
            check_func = check_tlc
        else:  # if checker is Apalache
            check_func = check_apalache

        try:
            result = check_func(
                tla_file_name=tla_file_name,
                files=checking_files_content,
                args=args,
                traces_dir=traces_dir,
            )
        except Exception as e:
            self.logger.error("Problem running {}: {}".format(checker, e))
            raise ModelCheckingError(e)

        return result

    def _check_sample_thread_worker(
        self,
        predicate,
        constants,
        checker,
        tla_file_name,
        checking_files_content,
        checker_params,
        mod_res,
        monitor_update_functions,
        result_considered_success: bool,
        original_predicate_name: str = None,
        traces_dir: Optional[str] = None,
    ):
        if original_predicate_name is None:
            original_predicate_name = predicate
        self.logger.debug("starting with {}".format(predicate))
        check_result = self._modelcheck_predicates(
            predicates=[predicate],
            constants=constants,
            checker=checker,
            tla_file_name=tla_file_name,
            checking_files_content=checking_files_content,
            checker_params=checker_params,
            traces_dir=traces_dir,
        )
        self.logger.debug("finished with {}".format(predicate))

        mod_res.lock.acquire()
        mod_res._finished_operators.append(original_predicate_name)
        mod_res._in_progress_operators.remove(original_predicate_name)

        if check_result.is_ok == result_considered_success:
            mod_res._successful.append(original_predicate_name)
        else:
            mod_res._unsuccessful.append(original_predicate_name)

        mod_res.lock.release()

        # in the current implementation, this will only return one trace (as a counterexample)
        if check_result.traces:
            mod_res._traces[original_predicate_name] = check_result.traces
            mod_res.add_trace_paths(original_predicate_name, check_result.trace_paths)

        for monitor_func in monitor_update_functions:
            monitor_func(res=mod_res)

    def check(
        self,
        invariants: List[str] = [],
        constants: Dict[str, Any] = {},
        checker: str = const_values.APALACHE,
        checker_params: Dict[str, str] = {},
        traces_dir: Optional[str] = None,
    ) -> ModelResult:

        if checker is not const_values.APALACHE:
            raise ValueError(
                "Currently, only the Apalache checker is supported. Support for TLC coming soon"
            )

        if self.parsable is False:
            raise self.last_parsing_error

        if invariants == []:
            invariants = [
                str(op)
                for op in self.operators
                if tla_helpers._default_invariant_criteria(str(op))
            ]

        constants = self.constants | constants

        mod_res = ModelResult(model=self, all_operators=invariants)

        for monitor in self.monitors:
            #  TODO: make monitors parallel
            monitor.on_check_start(res=mod_res)

        threads = []

        for invariant in invariants:
            thread = threading.Thread(
                target=self._check_sample_thread_worker,
                kwargs={
                    "predicate": invariant,
                    "constants": constants,
                    "checker": checker,
                    "tla_file_name": self.tla_file_path,
                    "checking_files_content": copy(self.files_contents),
                    "checker_params": checker_params,
                    "mod_res": mod_res,
                    "monitor_update_functions": [
                        m.on_check_update for m in self.monitors
                    ],
                    "result_considered_success": True,
                    "traces_dir": traces_dir,
                },
            )
            self.logger.debug(
                "starting thread {} for invariant {}".format(thread, invariant)
            )
            thread.start()
            threads.append(thread)
        threads.reverse()
        for thread in threads:
            thread.join()
            self.logger.debug("joining thread {}".format(thread))

        for monitor in self.monitors:
            monitor.on_check_finish(res=mod_res)

        self.all_checks.append(mod_res)
        return mod_res

    def sample(
        self,
        examples: List[str] = [],
        constants: Dict[str, Any] = {},
        checker: str = const_values.APALACHE,
        checker_params: Dict[str, str] = {},
        traces_dir: Optional[str] = None,
    ) -> ModelResult:

        if self.parsable is False:
            raise self.last_parsing_error

        if examples == []:
            # take all operators that are prefixed/suffixed with Ex
            examples = [
                str(op)
                for op in self.operators
                if tla_helpers._default_example_criteria(str(op))
            ]

        constants = self.constants | constants

        mod_res = ModelResult(model=self, all_operators=examples)

        for monitor in self.monitors:
            monitor.on_sample_start(res=mod_res)

        threads = []
        for example_predicate in examples:
            (
                negated_name,
                negated_content,
                negated_predicates,
            ) = tla_helpers.tla_file_with_negated_predicates(
                module_name=self.module_name, predicates=[example_predicate]
            )
            assert len(negated_predicates) == 1
            sampling_files_content = copy(self.files_contents)
            sampling_files_content.update({negated_name: negated_content})
            thread = threading.Thread(
                target=self._check_sample_thread_worker,
                kwargs={
                    "original_predicate_name": example_predicate,
                    "predicate": negated_predicates[0],
                    "constants": constants,
                    "checker": checker,
                    "tla_file_name": negated_name,
                    "checking_files_content": sampling_files_content,
                    "checker_params": checker_params,
                    "mod_res": mod_res,
                    "monitor_update_functions": [
                        m.on_sample_update for m in self.monitors
                    ],
                    "result_considered_success": False,
                    "traces_dir": traces_dir,
                },
            )
            thread.start()
            threads.append(thread)

        for thread in threads:
            thread.join()

        for monitor in self.monitors:
            monitor.on_sample_finish(res=mod_res)

        self._all_samples.append(mod_res)

        return mod_res

    def all_samples(self):
        return self._all_samples

    def last_sample(self):
        return self._all_samples[-1]

    def set_log_level(self, loglevel: str):
        numeric_level = getattr(logging, loglevel.upper(), None)
        if not isinstance(numeric_level, int):
            raise ValueError("Invalid log level: %s" % loglevel)
        self.logger.setLevel(numeric_level)

    def __init__(
        self,
        tla_file_path: str,
        init_predicate: str,
        next_predicate: str,
        files_contents: Dict[str, str] = {},
        constants: Dict[str, Any] = {},
        loglevel: str = "info",
    ) -> None:
        self.logger = modelator_helpers.create_logger(
            logger_name=__file__, loglevel=loglevel
        )
        # an entry file for the tla model
        self.tla_file_path = tla_file_path
        # init and next predicates, which are obligatory for all models
        self.init_predicate = init_predicate
        self.next_predicate = next_predicate

        # a dictionary file_name --> file_content, for relevant filenames
        self.files_contents = files_contents

        # a dcitionary of constant values relevant to the model
        self.constants = constants if constants is not None else {}

        # a list of results for all checks performed on this model
        self.all_checks = []

        # a list of results for all samples performed on this model
        self._all_samples = []

        # a list of monitors which track the progress of model actions
        self.monitors: List[ModelMonitor] = []

        self.autoparse = False

    def add_monitor(self, monitor: ModelMonitor):
        self.monitors.append(monitor)

    def remove_monitor(self, monitor: ModelMonitor):
        self.monitors.remove(monitor)

    def info(self) -> Dict[str, str]:
        return {
            "model_path": self.tla_file_path,
            "module_name": self.module_name,
            "variables": self.variables,
            "operators": self.operators,
            "init": self.init_predicate,
            "next": self.next_predicate,
            "constants": self.constants,
            "files": list(self.files_contents.keys()),
            "monitors": self.monitors,
        }
