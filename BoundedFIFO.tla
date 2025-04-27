---------------------------- MODULE BoundedFIFO ----------------------------
EXTENDS Naturals, Sequences
VARIABLES in, out
CONSTANT Message, N

ASSUME(N \in Nat) /\ (N > 0)

Inner(q) == INSTANCE InnerFifo

BNext(q) == /\ Inner(q)!Next
            /\ Inner(q)!BufRcv => (Len(q) < N)

Spec == \EE q : Inner(q)!Init /\ [][BNext(q)]_<<in, out, q>>
\* This spec can't be ran, this is the error:
\* TLC does not support temporal existential, nor universal, quantification over state variables.
=============================================================================
\* Modification History
\* Last modified Sun Apr 27 13:24:07 IST 2025 by gustavo.franke
\* Created Fri Feb 07 17:32:00 GMT 2025 by gustavo.franke
