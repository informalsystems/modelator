from modelator.modelator_shell import *
from modelator import const_values


m = Model.parse_file("modelator/samples/HelloFull.tla")
sample_res = m.sample()
check_res = m.check()
# m.typecheck()
