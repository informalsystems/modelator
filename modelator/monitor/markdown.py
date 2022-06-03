
from typing import Any
from modelator.monitor.content import MonitorSection
from modelator.monitor.model_monitor import ModelMonitor, ModelResult


class MarkdownModelMonitor(ModelMonitor):
    '''
    A monitor that writes all model action updates to a Markdown file.
    '''

    def __init__(self, filename):
        super().__init__()
        self.filename = filename
        self.fd = open(self.filename, 'w+', 1)
        self.fd.truncate(0)
        
        self.title: str = None
        self.sections: list[MonitorSection] = []

    def __enter__(self):
        return self
    
    def __exit__(self, exc_type, exc_value, trace):
        self.fd.close()

    def on_parse_start(self, res: ModelResult):
        self.title = f'⏳ Parsing {res.model()}...'
        self._write_content()

    def on_parse_finish(self, res: ModelResult):
        self.title = res.model()
        self._write_content()

    def on_sample_start(self, res: ModelResult):
        section = MonitorSection.create_from("Examples", res)
        self._add_section(section)
        self._write_content()

    def on_sample_update(self, res: ModelResult):
        last_section = self.sections[-1].update_with(res)
        self._update_last_section(last_section)
        self._write_content()

    def on_sample_finish(self, res: ModelResult):
        last_section = self.sections[-1].update_with(res)
        self._update_last_section(last_section)
        self._write_content()

    def on_check_start(self, res: ModelResult):
        section = MonitorSection.create_from("Invariants", res)
        self._add_section(section)
        self._write_content()

    def on_check_update(self, res: ModelResult):
        last_section = self.sections[-1].update_with(res)
        self._update_last_section(last_section)
        self._write_content()

    def on_check_finish(self, res: ModelResult):
        last_section = self.sections[-1].update_with(res)
        self._update_last_section(last_section)
        self._write_content()

    def _write_content(self):
        self.fd.truncate(0)
        self.fd.seek(0)
        
        self.fd.write(f'# {self.title}\n\n')
        self.fd.flush()
        
        for section in reversed(self.sections):
            self._write_section(section)
            self.fd.flush()

    def _write_section(self, section):
            self.fd.write(f'## {section.name}\n\n')
            self.fd.write(f'- Start time: {section.start_time}\n')
            if section.update_time is not None:
                self.fd.write(f'- Update time: {section.update_time}\n')
            self.fd.write('\n')
            
            for entry in section.entries:
                self.fd.write('### ')
                entry.status_position = self.fd.tell()
                self.fd.write(f'{str(entry.status)} {entry.name}\n\n')
                if entry.trace is not None:
                    self._write_table(entry.trace, columns=['A', 'B', 'C'])

    def _write_table(self, table, columns):
        for row in self._mk_table(table, columns):
            self.fd.write(row)
        self.fd.write('\n\n')

    def _add_section(self, section):
        self.sections.append(section)
    
    def _update_last_section(self, section):
        index = len(self.sections) - 1
        self.sections[index] = section

    def _mk_table(self, table:list[dict[Any, Any]], columns:list[str], column_width: int = 20):
        rows = []
        
        # build header
        column_names = '|'.join(s.center(column_width) for s in columns)
        separator = '|'.join('-' * column_width for _ in range(len(columns)))
        rows.append(f'|{column_names}|\n')
        rows.append(f'|{separator}|\n')
        
        # build body
        for entry in table:
            row = '|'.join(v.center(column_width) for k, v in entry.items())
            rows.append(f'|{row}|\n')
        
        return rows

test_traces = {
    'bbb': [
        {
            "A": "aaa",
            "B": "bbb",
            "C": "ccc",
        },
        {
            "A": "000",
            "B": "111",
            "C": "222",
        },
    ]
}

def test_add_section(m):
    input("Press key to on_check_start")
    res = ModelResult(None, inprogress=['aaa', 'bbb', 'ccc'])
    m.on_check_start(res)

    input("Press key to on_check_update")
    res = ModelResult(None, inprogress=['aaa'], successful=['ccc'], unsuccessful=['bbb'], traces=test_traces)
    m.on_check_update(res)

    input("Press key to on_check_finish")
    res = ModelResult(None, successful=['aaa', 'ccc'], unsuccessful=['bbb'], traces=test_traces)
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