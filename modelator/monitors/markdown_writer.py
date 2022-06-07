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
            self.fd.write(f'---\n')
            self.fd.write(f'## {section.name}\n\n')
            self.fd.write(f'- Start time: {section.start_time}\n')
            update_time = section.update_time if section.update_time else '-'
            self.fd.write(f'- Last update: {update_time}\n')
            self.fd.write('\n')
            
            for entry in section.entries:
                self.fd.write('### ')
                entry.status_position = self.fd.tell()
                self.fd.write(f'{str(entry.status)} {entry.name}\n\n')
                if entry.trace is not None:
                    self._write_trace(entry.trace, columns=['Variable', 'Previous value', 'Next value'])

    def _write_trace(self, trace, columns):
        for t in trace:
            self.fd.write(f'{t["name"]}\n\n')
            for row in self._mk_table(t["transition"], columns):
                self.fd.write(row)
            self.fd.write('\n\n')

    def _mk_table(self, table:list[dict[str,str]], columns:list[str], column_width: int = 25):
        rows = []
        
        # build header
        column_names = '|'.join(s.center(column_width) for s in columns)
        separator = '|'.join('-' * column_width for _ in range(len(columns)))
        rows.append(f'|{column_names}|\n')
        rows.append(f'|{separator}|\n')
        
        # build body
        for entry in table:
            row = '|'.join(
                MarkdownWriter._replace_special_characters(v).center(column_width) 
                for k, v in entry.items() if k in columns)
            rows.append(f'|{row}|\n')
        
        return rows

    def _replace_special_characters(s: str) -> str:
        s.replace('|->', '↦')