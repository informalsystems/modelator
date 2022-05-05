import os
from modelator.parse import parse



class Modelator:    
    
    def __init__(self, model_file_name=None) -> None:
        

        self.model_file_name = model_file_name
        if self.model_file_name is not None:
            self.load(self.model_file_name)
        
    def __repr__(self) -> str:
        if self.model_file_name is not None:
            return "Modelator instance for the model {}".format(self.model_file_name)
        else:
            return "Modelator instance without a model (use 'load' to load a model file)"


    def load(self, file_to_load):
        self.model_file_name = file_to_load
        self.model = open(file_to_load).read()
        print("Loaded file {}.\n Its content is:\n{}".format(self.model_file_name, self.model))
    
    def parse(self):        
        if self.model is None:
            print("ERROR: Model is not set yet. Use command `load <model_file>.tla`")
        else: 
            res, msg = parse(self.model)
            if res is True:
                print("File {} successfully parsed.".format(self.model_file_name))
            else:
                print("Error parsing {}: {}".format(self.model_file_name, msg))
        
        

def clear():
    os.system('cls' if os.name=='nt' else 'clear')
