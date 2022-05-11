import os
from modelator.parse import parse
from modelator.typecheck import typecheck



class Modelator:    
    
    def __init__(self, model_file_name=None, autoload = True) -> None:
                
        self.model_file_name = model_file_name
        self.autoload = autoload
        if self.autoload is True and self.model_file_name is not None:
            self.model = self.load(self.model_file_name, print_info=False)
        
    def __repr__(self) -> str:
        if self.model_file_name is not None:
            return "Modelator instance for the model {}".format(self.model_file_name)
        else:
            return "Modelator instance without a model (use 'load' to load a model file)"


    def load(self, file_to_load, print_info=True):
        self.model_file_name = file_to_load
        self.model = open(file_to_load).read()
        if print_info is True:
            print("Loaded file {}.\n Its content is:\n{}".format(self.model_file_name, self.model))
    
    def parse(self):        
        if self.model_file_name is None or (self.autoload is False and self.model is None):
            print("ERROR: Model is not set yet. Use command `load(<model_file>.tla)`")
        else: 
            if self.autoload is True:
                self.load(self.model_file_name, print_info=False)
            res, msg = parse(self.model)            
            if res is True:
                print("File {} successfully parsed.".format(self.model_file_name))
            else:
                msg.file_path = os.path.abspath(self.model_file_name)                 
                print(msg)
    
    def typecheck(self):
        if self.model_file_name is None or (self.autoload is False and self.model is None):
            print("ERROR: Model is not set yet. Use command `load(<model_file>.tla)`")
        else: 
            if self.autoload is True:
                self.load(self.model_file_name, print_info=False)
            res, msg = typecheck(self.model)
            if res is True:
                print("File {} typechecks.".format(self.model_file_name))
            else:
                msg.file_path = os.path.abspath(self.model_file_name)                
                print(msg)
        
def exp():
    print("check this type: samples/HelloFlawed.tla")
    print("check this type: modelator/samples/HelloFlawed.tla")
    print("check this type: python/modelator/samples/HelloFlawed.tla")
    print("check this type: /Users/ivan/Documents/codebase/modelator/python/modelator/samples/HelloFlawed.tla")
def clear():
    os.system('cls' if os.name=='nt' else 'clear')


def start():
    m = Modelator()
    m.load('modelator/samples/HelloFlawedType.tla')
    return m