from string import Template
from typing import Any
from modelator.itf import ITF

TEMPLATES_DIR = 'modelator/monitors/templates'
TRACE_COLUMNS = ['Variable', 'Value', 'Next value']


class HtmlWriter():
    
    def __init__(self, filename):
        self.filename = filename
        self.fd = open(self.filename, 'w+', 1)
        self.fd.truncate(0)
    
    def close(self):
        self.fd.close()
    
    def write_content(self, title, sections=[]):
        with open(f'{TEMPLATES_DIR}/html_monitor.html', 'r') as f:
            template = Template(f.read())
        html = template.substitute({
            'title': title, 
            'sections': self._make_html_for(sections)
        })
        self.fd.truncate(0)
        self.fd.seek(0)
        self.fd.write(html)
        self.fd.flush()

    def _make_html_for(self, sections):
        with open(f'{TEMPLATES_DIR}/html_section.html', 'r') as f:
            template = Template(f.read())
        time_format = '%Y-%m-%d %H:%M:%S'
        html_sections = []
        is_first_section = True
        for section in reversed(sections):
            if is_first_section:
                section_status = 'open="open"' 
                is_first_section = False
            else:
                section_status = ''
            html_section = template.substitute({
                'name': section.name, 
                'section_status': section_status,
                'startTime': section.start_time.strftime(time_format),
                'lastUpdate': section.update_time.strftime(time_format) if section.update_time else '-',
                'sectionEntries': self._make_html_entries_for(section)
            })
            html_sections.append(html_section)
        return '\n'.join(html_sections)

    def _make_html_entries_for(self, section):
        with open(f'{TEMPLATES_DIR}/html_section_entry.html', 'r') as f:
            template = Template(f.read())
        entries = []
        for entry in section.entries:
            status_color = entry.status.html_color()
            status_color_str = 'color: ' + status_color if status_color else ''
            if entry.trace is not None:
                html_trace = self._make_html_trace(entry.trace, columns=TRACE_COLUMNS)
            else:
                html_trace = ''
            entries.append(template.substitute({
                'status': entry.status, 
                'status_color': status_color_str,
                'name': entry.name,
                'trace': html_trace
            }))
        return '\n'.join(entries)

    def _make_html_trace(self, trace: list["ITF"], columns: list[str]) -> str:
        with open(f'{TEMPLATES_DIR}/html_trace.html', 'r') as f:
            template = Template(f.read())
        trace_txs = []
        for ix, step in enumerate(ITF.diff(trace)):
            trace_txs.append(template.substitute({
                'transition_name': f'State {ix} -> State {ix + 1}',
                'transition_variables': self._make_table(step, columns)
            }))
        return '\n'.join(trace_txs)

    def _make_table(self, transition:list[tuple[str,Any,Any]], columns:list[str]):
        # build header
        template_header_cell = Template('<th>$cell</th>')
        header = '\n'.join(template_header_cell.substitute({'cell': col}) for col in columns)
        header = '<tr>' + header + '</tr>'
        
        # build body
        template_body_cell = Template('<td>$cell</td>')
        rows = []
        for (varname, value1, value2) in transition:
            row = '\n'.join([
                template_body_cell.substitute({'cell': varname}),
                template_body_cell.substitute({'cell': HtmlWriter._replace_special_characters(value1)}),
                template_body_cell.substitute({'cell': HtmlWriter._replace_special_characters(value2)}),
                ])
            rows.append('<tr>' + row + '</tr>')
        rows = '\n'.join(rows)
        
        with open(f'{TEMPLATES_DIR}/html_table.html', 'r') as f:
            template = Template(f.read())
        return template.substitute({'header': header, 'body': rows})

    @staticmethod
    def _replace_special_characters(s: Any) -> Any:
        if isinstance(s, str):
            return s.replace('|->', '↦').replace('<', '&lt;').replace('>', '&gt;')
        else:
            return s
