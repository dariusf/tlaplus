---- MODULE Stress ----

EXTENDS Naturals

VARIABLE x
CONSTANT RM

vars == <<x>>

Init == x = 1

A ==
  /\ x < 0
  /\ x' = x + 1

A1 ==
  /\ x < 0
  /\ x' = x + 1
    /\ x < 0

B ==
  /\ UNCHANGED x

Send(y) == x = y
C ==
  /\ Send(x)

D ==
  \/
    /\ x = 1
    /\ x' = 2
  \/
    /\ x /= 1
    /\ x' = 3

E ==
  \/
    /\ x = 1
    /\ x' = 2
    /\
      \/ x = 2
      \/
        /\ x = 3
        /\ x = 1
  \/
    /\ x /= 1
    /\ x' = 3

F(z) == TRUE

G == [[ a |-> 1 ] EXCEPT !["a"] = 2]["a"] = 2

H == \A r \in {1, 2} : r = 1
H1 == \A s \in {1, 2} : \A r \in {1, 2} : r = s
H2 == [ r \in RM |-> "a" ]

Next ==
  \/ A
  \/ A1
  \/ B
  \/ C
  \/ D
  \/ E
  \/ F(1)
  \/ G
  \/ H

Spec == Init /\ [][Next]_vars

====
