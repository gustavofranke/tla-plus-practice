-------------------------- MODULE AsynchInterface --------------------------
(*
         |----------|      |----------|
         |          | val  |          |
         |          |----->|          |
         |          |----->|          |
         |  Sender  |  rdy | Receiver |
         |          |      |          |
         |          | ack  |          |
         |          |<-----|          |
         |----------|      |----------|

Data is sent on val, and the rdy and ack lines are used for synchronization.
The sender must wait for an acknowledgment (an Ack) for one data item
before it can send the next.
The interface uses the standard two-phase handshake protocol,
described by the following sample behavior:

| val = 26 |              | val = 37 |         | val = 37 |
| rdy = 0  |-- Send 37 -> | rdy = 1  |- Ack -> | rdy = 1  |- Send 4 ->
| ack = 0  |              | ack = 0  |         | ack = 1  |

| val = 4 |         | val = 4 |             | val = 19 |
| rdy = 0 |- Ack -> | rdy = 0 |- Send 19 -> | rdy = 1  |- Ack -> ...
| ack = 1 |         | ack = 0 |             | ack = 0  |

(It doesn’t matter what value val has in the initial state.)
*)
EXTENDS Naturals
CONSTANT Data
VARIABLES val, rdy, ack
TypeInvariant == /\ val \in Data
                 /\ rdy \in {0, 1}
                 /\ ack \in {0,1}
----------------------------------------------------------------------------
Init == /\ val \in Data
        /\ rdy \in {0,1}
        /\ ack = rdy
        
Send == /\ rdy = ack
        /\ val' \in Data
        /\ rdy' = 1 - rdy
        /\ UNCHANGED ack
              
Rcv == /\ rdy # ack
       /\ ack' = 1 - ack 
       /\ UNCHANGED <<val, rdy>>
       
Next == Send \/ Rcv

Spec == Init /\ [][Next]_<<val, rdy, ack>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Fri Apr 25 18:02:11 IST 2025 by gustavo.franke
\* Created Fri Feb 07 15:29:20 GMT 2025 by gustavo.franke
