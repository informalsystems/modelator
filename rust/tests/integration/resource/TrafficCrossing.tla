------------------------------ MODULE TrafficCrossing ------------------------------
\* This is an extention of the traffic example from https://git.io/JEY80
\* We have two crossing roads, 0 and 1; with two traffic lights, one for each road.
\* There can be multiple cars on the roads, each having a specific position.
\* Position 0 represents the road crossing.
\* 2021 Andrey Kuprianov, Informal Systems

EXTENDS Integers, FiniteSets

CONSTANTS 
  \* @typeAlias: CAR = [ road: Int, pos: Int ];
  \* @typeAlias: CARS = Int -> CAR;
  \* @typeAlias: LIGHT = Str;
  \* @typeAlias: LIGHTS = Int -> LIGHT;
  \* How many cars are there? 
  \* @type: Int;
  NUM_CARS

VARIABLES
  \* @type: LIGHTS;
  lights,
  \* @type: CARS;
  cars

Roads == {0, 1}
Color == {"red", "redyellow", "green", "yellow"}
Cars == 1..NUM_CARS
Positions == 1..NUM_CARS

\* Start with one light green, one red, and the cars distributed among the roads
DefaultInit == 
  /\ lights = [ road \in Roads |-> IF road = 0 THEN "green" ELSE "red" ]
  /\ cars \in [ Cars -> [ road: Roads, pos: Positions] ]
  /\ \A car1, car2 \in Cars:
       car1 /= car2 => cars[car1] /= cars[car2]


\* Auxiliary predicates

NextColor(c) == CASE c = "red" -> "redyellow"
                  [] c = "redyellow" -> "green"
                  [] c = "green" -> "yellow"
                  [] c = "yellow" -> "red"
                  [] OTHER -> "red" \* APALACHE requires OTHER

HasCarAt(road, pos) ==
  \E c \in Cars: 
    /\ cars[c].road = road
    /\ cars[c].pos = pos

CarAtCrossing ==
  \E c \in Cars : cars[c].pos = 0 

TrafficAllowed ==
  \E road \in Roads : lights[road] = "green"


\* Light actions

StopTraffic ==
  /\ TrafficAllowed
  /\ lights' = [ road \in Roads |-> NextColor(lights[road]) ]
  /\ UNCHANGED cars

AllowTraffic ==
  /\ ~TrafficAllowed
  /\ lights' = [ road \in Roads |-> NextColor(lights[road]) ]
  /\ UNCHANGED cars

LightActions == 
  \/ StopTraffic
  \/ AllowTraffic


\* Car actions

MoveForward ==
  /\ \E c \in Cars:
     LET car == cars[c] IN
       /\ car.pos > 1
       /\ ~ HasCarAt(car.road, car.pos-1)
       /\ cars' = [cars EXCEPT ![c] = [@ EXCEPT !.pos = @ - 1 ] ]
  /\ UNCHANGED lights

CrossStreet ==
  /\ \E c \in Cars:
     LET car == cars[c] IN
       /\ car.pos = 1
       /\ lights[car.road] = "green"
       /\ ~ HasCarAt(car.road, car.pos-1)
       /\ cars' = [cars EXCEPT ![c] = [@ EXCEPT !.pos = 0 ] ]
  /\ UNCHANGED lights

\* When leaving the crossing the car gets at the end of some road
LeaveCrossing ==
  /\ \E c \in Cars:
     LET car == cars[c] IN
       /\ car.pos = 0
       /\ \E road \in Roads : \E pos \in Positions :
          /\ \A c2 \in Cars:
               \/ cars[c2].road /= road
               \/ cars[c2].pos < pos
          /\ cars' = [cars EXCEPT ![c] = [road |-> road, pos |-> pos ] ]
  /\ UNCHANGED lights

CarActions ==
  \/ CrossStreet
  \/ LeaveCrossing
  \/ MoveForward


DefaultNext ==
  \* The rule is that any car at the crossing when no traffic allowed
  \* should leave it before the traffic is allowed again
  IF ~TrafficAllowed /\ CarAtCrossing THEN
    LeaveCrossing
  ELSE
    \/ LightActions
    \/ CarActions


\* Invariants

NoDoubleLights ==
  \A r1, r2 \in Roads:
    r1 /= r2 => lights[r1] /= lights[r2]

NoRoadCollisions == 
  \A c1, c2 \in Cars:
    \/ cars[c1].pos = 0 \* we treat crossing collisions separately
    \/ c1 /= c2 => cars[c1] /= cars[c2]

NoCrossingCollisions == 
  \A c1, c2 \in Cars:
    c1 /= c2 => ~ (cars[c1].pos = 0 /\ cars[c2].pos = 0)


=============================================================================
