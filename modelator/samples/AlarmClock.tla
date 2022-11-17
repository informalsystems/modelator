----- MODULE AlarmClock -----

EXTENDS Naturals, Sequences

VARIABLES
  \* @typeAlias: state = { hr: Int, alarmHr: Int, alarmOn: Bool };
  \* @type: Int;
  hr,
  \* @type: Int;
  alarmHr,
  \* @type: Bool;
  alarmOn

Init ==
    /\ hr \in (1 .. 12)
    /\ alarmHr \in (1..12)
    /\ alarmOn = FALSE
AdvanceHour ==
    /\ hr' = IF hr /= 12 THEN hr + 1 ELSE 1
    /\ UNCHANGED <<alarmHr, alarmOn>>
SetAlarm ==
    /\ alarmHr' \in (1..12)
    \* Oops, forgot to set alarmOn' = TRUE
    /\ UNCHANGED <<hr, alarmOn>>
Ring ==
    /\ alarmOn \* Oops, alarmOn is always FALSE
    /\ hr = alarmHr
    /\ alarmOn' = FALSE
    /\ UNCHANGED <<alarmHr, hr>>

Next ==
  \/ AdvanceHour
  \/ SetAlarm
  \/ Ring

============================
