# HourClock

## Examples

### (OK) ExThreeHours

State 0 -> State 1
| state component | prev_state | next_state |
| ----- | ----- | ----- |
|  .action.name    |                   Null   |       IBCTransferSendPacket |
|  .action.packet |  |  [ amount : 2, denom : 2, from : 2, id : 0, 

### (FAIL) ExFullRun

## Invariants

### (OK) InvNoOverflow 



### (FAIL) InvNoUnderflow 

State 0 -> State 1
| state component | prev_state | next_state |
| ----- | ----- | ----- |
|  .action.name    |                   Null   |       IBCTransferSendPacket |
|  .action.packet |  |  [ amount : 2, denom : 2, from : 2, id : 0, 

State 1 -> State 2
| state component | prev_state | next_state |
| ----- | ----- | ----- |
|  .action.name    |                   Null   |       IBCTransferSendPacket |
|  .action.packet |  |  [ amount : 2, denom : 2, from : 2, id : 0, 