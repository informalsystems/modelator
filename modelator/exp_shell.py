from modelator.modelator_shell import *
from modelator import const_values
from modelator.monitors.html_monitor import HtmlModelMonitor
from modelator.monitors.markdown_monitor import MarkdownModelMonitor

m = Model.parse_file("modelator/samples/HelloFull.tla")
m.add_monitor(MarkdownModelMonitor('status.md'))
m.add_monitor(HtmlModelMonitor('status.html'))
sample_res = m.sample()
check_res = m.check()
