from datetime import datetime
from enum import Enum
from typing_extensions import Self

from modelator.ModelResult import ModelResult

class Status(Enum):
    success = 'success'
    failure = 'failure'
    inprogress = 'inprogress'
    unknown = 'unknown'

    def __str__(self):
        match self:
            case Status.success: 
                return '✅'
            case Status.failure:
                return '❌'
            case Status.inprogress:
                return '⏳'
            case _:
                return '❓'
    
    def html_color(self):
        match self:
            case Status.success: 
                return 'green'
            case Status.failure:
                return 'red'
            case Status.inprogress:
                return ''
            case Status.unknown:
                return 'yellow'

class MonitorEntry:
    '''
    An entry in a section.
    '''
    status_position: int = None
    
    def __init__(self, name: str, status: Status=None, trace=None):
        self.name = name
        self.status = status
        self.trace = trace

    def set_status_position(self, position):
        self.status_position = position

class MonitorSection:
    '''
    A section is either a Sample or an Invariant.
    '''
    def __init__(self, name: str, entries: list[MonitorEntry], time: datetime):
        self.name = name
        self.entries = entries
        self.start_time = time
        self.update_time = None

    @staticmethod
    def all_entries_from(res: ModelResult):
        inprogress = [MonitorEntry(op, Status.inprogress) for op in res.inprogress()]
        successful = [MonitorEntry(op, Status.success, trace=res.traces(op)) for op in res.successful()]
        unsuccessful = [MonitorEntry(op, Status.failure, trace=res.traces(op)) for op in res.unsuccessful()]
        entries = inprogress+successful+unsuccessful
        return sorted(entries, key=lambda e: e.name)

    def create_from(name: str, res: ModelResult) -> Self:
        entries = MonitorSection.all_entries_from(res)
        return MonitorSection(name, entries=entries, time=res.time())

    def update_with(self, res: ModelResult) -> Self:
        self.entries = MonitorSection.all_entries_from(res)
        self.update_time = res.time()
        return self
