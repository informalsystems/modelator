
from datetime import datetime
from enum import Enum
from typing_extensions import Self

from modelator.monitor.model_monitor import ModelResult


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
            case _:
                return '❓'
        

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

    def create_from(name: str, res: ModelResult) -> Self:
        inprogress = [MonitorEntry(op, Status.inprogress) for op in res.inprogress()]
        successful = [MonitorEntry(op, Status.success) for op in res.successful()]
        unsuccessful = [MonitorEntry(op, Status.failure, trace=res.traces(op)) for op in res.unsuccessful()]
        return MonitorSection(name, entries=inprogress+successful+unsuccessful, time=res.time())

    def update_with(self, res: ModelResult) -> Self:
        inprogress = [MonitorEntry(op, Status.inprogress) for op in res.inprogress()]
        successful = [MonitorEntry(op, Status.success) for op in res.successful()]
        unsuccessful = [MonitorEntry(op, Status.failure, trace=res.traces(op)) for op in res.unsuccessful()]
        
        self.entries = inprogress+successful+unsuccessful
        self.update_time = res.time()
        return self
