from cmd2 import Cmd
from modelator.parse import parse
from importlib.resources import path
import os
from typing import IO

class ModelatorPrompt(Cmd):
    prompt = "modelator >> "


    
    def __init__(self) -> None:
        super().__init__()

        self.model = None
        self.model_file_name = None


    def do_parse(self, inp):
        'Parse the .tla file'
        if self.model is None:
            self.poutput("ERROR: Model is not set yet. Use command `load <model_file>.tla`")
        else: 
            res, msg = parse(self.model)
            if res is True:
                self.poutput("File {} successfully parsed.".format(self.model_file_name))
            else:
                self.poutput("Error parsing {}: {}".format(self.model_file_name, msg))
        
        

    def do_clear(self, line):
        os.system('cls' if os.name=='nt' else 'clear')

    def do_load(self, file_to_load):
        self.model_file_name = file_to_load
        self.model = open(file_to_load).read()
        self.poutput("Loaded file {}.\n Its content is:\n{}".format(self.model_file_name, self.model))


    
    def default(self, line: str) -> None:
        if line == "x" or line == 'EOF':
            return self.do_exit(line)
        else:
            super().default(line)

    

if __name__=="__main__":
    app = ModelatorPrompt()
    app.cmdloop()

