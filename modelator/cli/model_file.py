import os
import pickle
from pathlib import Path
from typing import Dict, Optional, Tuple

from modelator.Model import Model

# File that stores the serialized object of the current model.
MODEL_FILE_NAME = ".model.pickle"


class ModelFile:
    """
    Ser/Deserialize a model's instance and optionally a config file into a
    pickle file.
    """

    @staticmethod
    def load(
        log_level: Optional[str] = None,
    ) -> Tuple[Optional[Model], Optional[Dict], Optional[str]]:

        if not ModelFile.exists():
            return None, None, None

        with open(MODEL_FILE_NAME, "rb") as f:
            data = pickle.load(f)

            try:
                model = data["model"]
                config = data["config"]
                config_path = data["config_path"]
            except (KeyError, TypeError) as e:
                print(f"Error in saved file: {e}")
                return None, None, None

            if log_level:
                model.set_log_level(log_level)

            return model, config, config_path

    @staticmethod
    def save(model, config=None, config_path=None):
        """
        Save serialized model object to a file
        """
        data = {"model": model, "config": config, "config_path": config_path}
        with open(MODEL_FILE_NAME, "wb") as f:
            pickle.dump(data, f)

    @staticmethod
    def exists():
        return Path(MODEL_FILE_NAME).is_file()

    @staticmethod
    def clean() -> bool:
        try:
            os.remove(MODEL_FILE_NAME)
            return True
        except OSError:
            return False
