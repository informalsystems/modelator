import os
from typing import Dict

def get_auxiliary_tla_files(model_name: str) ->  Dict[str, str]:
    dir = os.path.dirname(os.path.abspath(model_name))            
    tla_files = [f for f in os.listdir(dir) if os.path.isfile(os.path.join(dir, f)) and f.split('.')[-1] in ["tla", "cfg"]]

    files = {}
    for file_name in tla_files:
        files[file_name] = open(os.path.join(dir, file_name)).read()

    return files
