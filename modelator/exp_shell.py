from modelator.modelator_shell import *


m = Model.parse_file("modelator/samples/HelloFull.tla")
res = m.sample()
# m.typecheck()
