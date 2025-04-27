-------------------------- MODULE MemoryInterface --------------------------
(*
                   |----------|      
|-----------|      |          |      |-----|
| Processor |<---> |          |      |  M  |
|-----------|      |          |      |  E  |
                   |  memInt  |<---> |  M  |
|-----------|      |          |      |  O  |
| Processor |<---> |          |      |  R  |
|-----------|      |          |      |  Y  |
                   |----------|      |-----|
*)

VARIABLE memInt
CONSTANTS 
    Send(_, _, _, _), \* A Send(p,d,memInt,memInt') step represents processor p sending value d to the memory.
    Reply(_, _, _, _), \* A Reply(p,d,memInt,memInt') step represents the memory sending value d to processor p.
    InitMemInt, \* The set of possible initial values of memInt.
    Proc, \* The set of processor identifiers.
    Adr, \* The set of memory addresses.
    Val \* The set of memory values.

ASSUME \A p, d, miOld, miNew : /\ Send(p, d, miOld, miNew) \in BOOLEAN
                               /\ Reply(p, d, miOld, miNew) \in BOOLEAN
                   

\* The set of all requests; a read specifies an address, a write specifies an address and a value.
MReq == [op: {"Rd"}, adr: Adr] \union [op: {"Wr"}, adr: Adr, val: Val]

\* An arbitrary value not in Val.
NoVal == CHOOSE v : v \notin Val
=============================================================================
\* Modification History
\* Last modified Sun Apr 27 12:16:48 IST 2025 by gustavo.franke
\* Created Fri Feb 07 17:39:28 GMT 2025 by gustavo.franke
