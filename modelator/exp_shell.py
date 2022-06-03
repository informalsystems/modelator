from modelator.modelator_shell import *

print("hi")

m = Model.parse_file("modelator/samples/Hello.tla")
m.typecheck()
