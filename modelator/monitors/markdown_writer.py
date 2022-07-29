from typing import Any
from modelator.itf import ITF

TRACE_COLUMNS = ['Variable', 'Value', 'Next value']


class MarkdownWriter():
    
    def __init__(self, filename):
        self.filename = filename
        self.fd = open(self.filename, 'w+', 1)
        self.fd.truncate(0)
    
    def close(self):
        self.fd.close()
    
    def write_content(self, title, sections=[]):
        self.fd.truncate(0)
        self.fd.seek(0)
        
        self.fd.write(f'# {title}\n\n')
        self.fd.flush()
        
        for section in reversed(sections):
            self._write_section(section)
            self.fd.flush()

    def _write_section(self, section):
        time_format = '%Y-%m-%d %H:%M:%S'
        self.fd.write(f'---\n')
        self.fd.write(f'## {section.name}\n\n')
        self.fd.write(f'- Start time: {section.start_time.strftime(time_format)}\n')
        update_time = section.update_time.strftime(time_format) if section.update_time else '-'
        self.fd.write(f'- Last update: {update_time}\n')
        self.fd.write('\n')
        
        for entry in section.entries:
            self.fd.write('### ')
            entry.status_position = self.fd.tell()
            self.fd.write(f'{str(entry.status)} {entry.name}\n\n')
            if entry.trace is not None:
                self._write_trace(entry.trace, columns=TRACE_COLUMNS)

    def _write_trace(self, trace, columns):
        for ix, step in enumerate(ITF.diff(trace)):
            self.fd.write(f'State {ix} -> State {ix + 1}\n\n')
            for row in self._make_table(step, columns):
                self.fd.write(row)
            self.fd.write('\n\n')

    def _make_table(self, transition:list[tuple[str,Any,Any]], columns:list[str], column_width: int = 25):
        rows = []
        
        # build header
        column_names = '|'.join(s.center(column_width) for s in columns)
        separator = '|'.join('-' * column_width for _ in range(len(columns)))
        rows.append(f'|{column_names}|\n')
        rows.append(f'|{separator}|\n')
        
        # build body
        for (varname, value1, value2) in transition:
            row = '|'.join([
                varname.center(column_width),
                MarkdownWriter._replace_special_characters(value1).center(column_width),
                MarkdownWriter._replace_special_characters(value2).center(column_width),
                ])
            rows.append(f'|{row}|\n')
        
        return rows

    @staticmethod
    def _replace_special_characters(s: Any) -> str:
        if isinstance(s, str):
            return s.replace('|->', '↦')
        else:
            return str(s)
