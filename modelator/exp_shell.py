from modelator.modelator_shell import *
from modelator import const_values
from modelator.monitors.markdown import MarkdownModelMonitor

m = Model.parse_file("modelator/samples/HelloFull.tla")
mon = MarkdownModelMonitor('status.md')
m.add_monitor(mon)
sample_res = m.sample()
check_res = m.check()
# m.typecheck()
