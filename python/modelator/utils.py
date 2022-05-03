import re

#TODO: add tests for these methods

def extract_tla_module_name(tla_file_content: str):
    match = re.search("-+[ ]*MODULE[ ]*(?P<moduleName>\w+)[ ]*-+", tla_file_content)
    if match is None:
        return None
    return match.group('moduleName')


def extract_parse_error(parser_output: str):
    report = []
    reportActive = False
    for line in parser_output.splitlines():
    
        if line == "Residual stack trace follows:":
            break

        if reportActive is True:
            report.append(line)

        if line == "***Parse Error***":
            reportActive = True
                
    if len(report) == 0:
        return None
    else:
        return "\n".join(report)        
