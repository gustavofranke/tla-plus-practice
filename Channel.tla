------------------------------ MODULE Channel ------------------------------
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
VARIABLE chan \* A record with val, rdy, and ack fields. If r is such a record, then r.val is its val field.

TypeInvariant == chan \in [val: Data, rdy: {0, 1}, ack: {0, 1}]
-----------------------------------------------------------------------------
Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy
        
Send(d) == /\ chan.rdy = chan.ack \* The following chan' are all equivalent:
\*         /\ chan' = [val |-> d, rdy |-> 1 - chan.rdy, ack |-> chan.ack]
\*         /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1- chan.rdy]
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]
           
Rcv == /\ chan.rdy # chan.ack
       /\ chan' = [chan EXCEPT !.ack = 1 - @]
       
Next == (\E d \in Data : Send(d)) \/ Rcv

Spec == Init /\ [][Next]_chan
=============================================================================
\* Modification History
\* Last modified Fri Apr 25 21:18:51 IST 2025 by gustavo.franke
\* Created Fri Feb 07 16:19:43 GMT 2025 by gustavo.franke
