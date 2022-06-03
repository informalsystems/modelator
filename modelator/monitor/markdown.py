
from typing import Any
from modelator.monitor.content import MonitorSection
from modelator.monitor.markdown_writer import MarkdownWriter
from modelator.monitor.model_monitor import ModelMonitor, ModelResult

class MarkdownModelMonitor(ModelMonitor):
    '''
    A monitor that writes all model action updates to a Markdown file.
    '''

    def __init__(self, filename):
        super().__init__()
        self.writer = MarkdownWriter(filename)
        
        self.title: str = None
        self.sections: list[MonitorSection] = []

    def __enter__(self):
        return self
    
    def __exit__(self, exc_type, exc_value, trace):
        self.writer.close()

    def on_parse_start(self, res: ModelResult):
        self.title = f'⏳ Parsing {res.model()}...'
        self.write_file()

    def on_parse_finish(self, res: ModelResult):
        self.title = res.model()
        self.write_file()

    def on_sample_start(self, res: ModelResult):
        self._add_section(MonitorSection.create_from("Examples", res))
        self.write_file()

    def on_sample_update(self, res: ModelResult):
        last_section = self.sections[-1].update_with(res)
        self._update_last_section(last_section)
        self.write_file()

    def on_sample_finish(self, res: ModelResult):
        last_section = self.sections[-1].update_with(res)
        self._update_last_section(last_section)
        self.write_file()

    def on_check_start(self, res: ModelResult):
        self._add_section(MonitorSection.create_from("Invariants", res))
        self.write_file()

    def on_check_update(self, res: ModelResult):
        last_section = self.sections[-1].update_with(res)
        self._update_last_section(last_section)
        self.write_file()

    def on_check_finish(self, res: ModelResult):
        last_section = self.sections[-1].update_with(res)
        self._update_last_section(last_section)
        self.write_file()

    def write_file(self):
        self.writer.write_content(self.title, self.sections)

    def _add_section(self, section):
        self.sections.append(section)
    
    def _update_last_section(self, section):
        index = len(self.sections) - 1
        self.sections[index] = section


test_traces = {
    'Inv2': [
        {
            'name': 'State 0 -> State 1',
            'transition': [
                {
                    "Variable": "x",
                    "Previous": "0",
                    "Next": "1",
                },
                {
                    "Variable": "b",
                    "Previous": "[foo |-> \"spam\"]",
                    "Next": "[foo |-> \"spam spam\"]",
                },
            ]
        },
        {
            'name': 'State 1 -> State 2',
            'transition': [
                {
                    "Variable": "x",
                    "Previous": "1",
                    "Next": "2",
                },
                {
                    "Variable": "b",
                    "Previous": "[foo |-> \"spam spam\"]",
                    "Next": "[foo |-> \"spam spam eggs\"]",
                },
            ]
        },
    ]
}

def test_add_section(m):
    input("Press key to on_check_start")
    res = ModelResult(None, inprogress=['Inv1', 'Inv2', 'Inv3'])
    m.on_check_start(res)

    input("Press key to on_check_update")
    res = ModelResult(None, inprogress=['Inv1'], successful=['Inv3'], unsuccessful=['Inv2'], traces=test_traces)
    m.on_check_update(res)

    input("Press key to on_check_finish")
    res = ModelResult(None, successful=['Inv1', 'Inv3'], unsuccessful=['Inv2'], traces=test_traces)
    m.on_check_finish(res)

mon = None

def test(filename):
    global mon
    mon = MarkdownModelMonitor(filename)

    input("Press key to on_parse_start")    
    mon.on_parse_start(ModelResult(model='ModelName'))

    input("Press key to on_parse_finish")
    mon.on_parse_finish(ModelResult(model='ModelName'))

    test_add_section(mon)
    test_add_section(mon)