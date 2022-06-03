from modelator.modelator_shell import *

print("hi")

m = Model.parse_file("modelator/samples/HelloFull.tla")
m.sample(examples=["Inv2"])
# m.typecheck()
