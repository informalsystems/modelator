----- MODULE HourClockTraits -----

EXTENDS HourClock

ExThreeHours == hr = 3

ExHourDecrease == hr' < hr

\* @type: Seq($state) => Bool;
ExFullRun(trace) ==
    /\ Len(trace) = 12
    /\ \A s1, s2 \in DOMAIN trace:
           s1 /= s2 => trace[s1].hr /= trace[s2].hr


InvNoOverflow  == hr <= 12
InvNoUnderflow  == hr >= 1

InvExThreeHours == ~ExThreeHours
InvExHourDecrease == ~ExHourDecrease

\* @type: Seq($state) => Bool;
InvExFullRun(trace) == ~ExFullRun(trace)

==================================
