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
    def load(log_level: Optional[str] = None) -> Tuple[Optional[Model], Optional[Dict]]:

        if not ModelFile.exists():
            return None, None

        with open(MODEL_FILE_NAME, "rb") as f:
            data = pickle.load(f)
            model = data["model"]
            config = data["config"]
            if log_level:
                model.set_log_level(log_level)
            return model, config

    @staticmethod
    def save(model, config=None):
        """
        Save serialized model object to a file
        """
        data = {"model": model, "config": config}
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
