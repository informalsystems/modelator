import os
import pickle
from pathlib import Path
from typing import Optional

from modelator.Model import Model

# File that stores the serialized object of the current model.
MODEL_FILE_NAME = ".model.pickle"


class ModelFile:
    """
    Ser/Deserialize a model's instance into a pickle file.
    """

    @staticmethod
    def load(log_level: Optional[str] = None) -> Optional[Model]:

        if not ModelFile.exists():
            return None

        with open(MODEL_FILE_NAME, "rb") as f:
            model = pickle.load(f)
            if log_level:
                model.set_log_level(log_level)
            return model

    @staticmethod
    def save(model):
        """
        Save serialized model object to a file
        """
        with open(MODEL_FILE_NAME, "wb") as f:
            pickle.dump(model, f)

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
