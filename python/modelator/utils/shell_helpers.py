
from .. import constants


class ConfigValues(dict):
    def __init__(self) -> None:
        self.config_keys = set([
            constants.INIT, 
            constants.INVARIANT, 
            constants.NEXT,
            constants.APALACHE_NUM_STEPS])        

    
    
    # def __getitem__(self, __k: _KT) -> _VT:
    def __getitem__(self, __k):
        return super().__getitem__(__k)

    # def __setitem__(self, __k: _KT, __v: _VT) -> None:
    def __setitem__(self, __k, __v) -> None:
        if __k not in self.config_keys:
            print("The allowed config values are {}".format(self.config_keys))
            return
        return super().__setitem__(__k, __v)



