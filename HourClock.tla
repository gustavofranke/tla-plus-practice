----------------------------- MODULE HourClock -----------------------------
(*

A digital clock that displays only the hour.
To make the system completely trivial, we ignore the relation between the
display and the actual time.
The hour clock is then just a device whose display cycles through the values 1 through 12.

A typical behavior of the clock is the sequence
[hr = 11] -> [hr = 12] -> [hr = 1] -> [hr = 2] -> ...
of states, where [hr = 11] is a state in which the variable hr has the value 11.
*)
EXTENDS Naturals
VARIABLE hr
HCini == hr \in (1..12)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC == HCini /\ [][HCnxt]_hr
-------
THEOREM HC => []HCini
=============================================================================
\* Modification History
\* Last modified Fri Apr 25 17:21:34 IST 2025 by gustavo.franke
\* Created Fri Feb 07 15:11:30 GMT 2025 by gustavo.franke
