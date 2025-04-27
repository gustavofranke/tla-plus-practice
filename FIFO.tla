-------------------------------- MODULE FIFO --------------------------------
CONSTANT Message
VARIABLES in, out

Inner(q) == INSTANCE InnerFifo
\*Observe that the instance statement is an abbreviation for
\*Inner(q ) == INSTANCE InnerFifo WITH q <- q, in <- in, out <-out, Message <- Message
Spec == \EE q : Inner(q)!Spec
\* This spec can't be ran, this is the error:
\* TLC does not support temporal existential, nor universal, quantification over state variables.
=============================================================================
\* Modification History
\* Last modified Sun Apr 27 13:22:48 IST 2025 by gustavo.franke
\* Created Fri Feb 07 17:21:49 GMT 2025 by gustavo.franke
