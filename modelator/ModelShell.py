from copy import copy
import logging
import os
import threading


from typing import Any, Dict, List, Optional, Union, final
from typing_extensions import Self
from modelator import ModelResult, const_values


from modelator.Model import Model
from watchdog.observers import Observer

from watchdog.events import FileSystemEventHandler

from modelator.utils.model_exceptions import ModelError, ModelParsingError
from modelator.utils import tla_helpers


class ModelShell(Model):
    @classmethod
    def parse_file(
        cls, file_name: str, init: str = "Init", next: str = "Next"
    ) -> Union[Self, ModelError]:

        auxiliary_files = tla_helpers.get_auxiliary_tla_files(file_name)

        # TODO: how to handle .cfg files? They are actually necessary for TLC

        m = ModelShell(
            tla_file_path=file_name,
            init_predicate=init,
            next_predicate=next,
            files_contents=auxiliary_files,
        )
        # a member function which will raise a ModelParsingError exception in case of problems
        try:
            m._parse()
        except ModelError as e:
            print(e)
        except Exception as e:
            logging.error("Unexpected exception: {}".format(e))
        else:
            return m

    def typecheck(self) -> Optional[ModelError]:
        try:
            super().typecheck()
        except ModelError as e:
            print(e)
        except Exception as e:
            self.logger.error("Unexpected exception: {}".format(e))

    def check(
        self,
        invariants: List[str] = None,
        model_constants: Dict = None,
        checker: str = const_values.APALACHE,
        checker_params: Dict = None,
    ) -> ModelResult:
        try:
            return super().check(invariants, model_constants, checker, checker_params)
        except ModelError as e:
            print(e)
        except Exception as e:
            self.logger.error("Unexpected exception: {}".format(e))

    def sample(
        self,
        examples: List[str] = None,
        model_constants: Dict = None,
        checker: str = const_values.APALACHE,
        checker_params: Dict = None,
    ) -> ModelResult:

        try:
            return super().sample(examples, model_constants, checker, checker_params)
        except ModelError as e:
            print(e)
        except Exception as e:
            self.logger.error("Unexpected exception: {}".format(e))

    def __init__(
        self,
        tla_file_path: str,
        init_predicate: str,
        next_predicate: str,
        files_contents: Dict[str, str] = None,
        constants: Dict[str, Any] = None,
    ) -> None:

        super().__init__(
            tla_file_path, init_predicate, next_predicate, files_contents, constants
        )

        self.autoload = True
        self.auto_parse_file()
        # self.load_observer = Observer()
        # self.autoloadhandler = FileSystemEventHandler()
        # self.autoloadhandler.on_modified = self._load_on_modified
        # self.old = 0
        # self.load_observer.schedule(
        #     self.autoloadhandler, os.path.abspath(self.tla_file_path), recursive=True
        # )
        # self.load_observer.start()

    def _load_on_modified(self, event):
        if event.is_directory:
            return None

        statbuf = os.stat(event.src_path)
        self.new = statbuf.st_mtime
        if (self.new - self.old) > 0.5:
            # this is a real event
            self.files_contents[self.tla_file_path] = open(event.src_path).read()

            self.old = self.new

    def auto_parse_file(self):
        self.autoparse = True
        self.observer = Observer()
        self.autohandler = FileSystemEventHandler()
        self.autohandler.on_modified = self._parse_on_modified
        self.old = 0
        self.observer.schedule(
            self.autohandler, os.path.abspath(self.tla_file_path), recursive=True
        )
        self.observer.start()

    def _parse_on_modified(self, event):
        if event.is_directory:
            return None

        statbuf = os.stat(event.src_path)
        self.new = statbuf.st_mtime
        if (self.new - self.old) > 0.5:
            # this is a real event
            self.files_contents[self.tla_file_path] = open(event.src_path).read()
            try:
                self._parse()
            except ModelError as e:
                self.parsable = False
                print(e)
            finally:
                self.old = self.new

    def stop_auto_parse(self):
        self.observer.stop()
        self.observer.join()
