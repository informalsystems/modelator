from modelator.ModelMonitor import ModelMonitor
from modelator.ModelResult import ModelResult
from modelator.itf import ITF
from modelator.monitors.content import MonitorSection
from modelator.monitors.html_writer import HtmlWriter


class HtmlModelMonitor(ModelMonitor):
    """
    A monitor that writes all model action updates to an HTML file.
    """

    def __init__(self, filename):
        super().__init__()
        self.writer = HtmlWriter(filename)

        self.title: str = None
        self.sections: list[MonitorSection] = []

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, trace):
        self.writer.close()

    def on_parse_start(self, res: ModelResult):
        self.title = f"⏳ Parsing {res.model().tla_file_path}..."
        self.write_file()

    def on_parse_finish(self, res: ModelResult):
        self._update_title(res)
        self.write_file()

    def on_sample_start(self, res: ModelResult):
        self._update_title(res)
        self._add_section(MonitorSection.create_from("Examples", res))
        self.write_file()

    def on_sample_update(self, res: ModelResult):
        last_section = self.sections[-1]
        self._set_last_section(last_section.update_with(res))
        self.write_file()

    def on_sample_finish(self, res: ModelResult):
        last_section = self.sections[-1]
        self._set_last_section(last_section.update_with(res))
        self.write_file()

    def on_check_start(self, res: ModelResult):
        self._update_title(res)
        self._add_section(MonitorSection.create_from("Invariants", res))
        self.write_file()

    def on_check_update(self, res: ModelResult):
        last_section = self.sections[-1]
        self._set_last_section(last_section.update_with(res))
        self.write_file()

    def on_check_finish(self, res: ModelResult):
        last_section = self.sections[-1]
        self._set_last_section(last_section.update_with(res))
        self.write_file()

    def write_file(self):
        self.writer.write_content(self.title, self.sections)

    def _update_title(self, res):
        self.title = res.model().module_name
        if res.parsing_error is True:
            self.title = self.title + ": parsing problem!"

    def _add_section(self, section):
        self.sections.append(section)

    def _set_last_section(self, section):
        index = len(self.sections) - 1
        self.sections[index] = section


test_traces = {
    "Inv2": [
        ITF({"x": 0, "y": 1, "f": '["foo" |-> "spam"]'}),
        ITF({"x": 1, "y": 1, "f": '["foo" |-> "spam spam"]'}),
        ITF({"x": 2, "y": 100, "f": '["foo" |-> "spam spam eggs"]'}),
    ]
}


class Model:
    tla_file_name = "foo/bar/ModuleName.tla"
    module_name = "ModuleName"


monitor = None


def test_add_section():
    input("Press key to on_check_start")
    res = ModelResult(model=Model())
    res._in_progress_operators = ["Inv1", "Inv2", "Inv3"]
    monitor.on_check_start(res)

    input("Press key to on_check_update")
    res = ModelResult(model=Model())
    res._in_progress_operators = ["Inv1"]
    res._successful = ["Inv3"]
    res._unsuccessful = ["Inv2"]
    res._traces = test_traces
    monitor.on_check_update(res)

    input("Press key to on_check_finish")
    res = ModelResult(model=monitor)
    res._in_progress_operators = []
    res._successful = ["Inv1", "Inv3"]
    res._unsuccessful = ["Inv2"]
    res._traces = test_traces
    monitor.on_check_finish(res)


def test(filename):
    global monitor
    monitor = HtmlModelMonitor(filename)

    input("Press key to on_parse_start")
    monitor.on_parse_start(ModelResult(model=Model()))

    input("Press key to on_parse_finish")
    monitor.on_parse_finish(ModelResult(model=Model()))

    test_add_section()
    test_add_section()
