----------------------------- MODULE InnerFifo -----------------------------
EXTENDS Naturals, Sequences
CONSTANT Message
VARIABLES in, out, q
InChan  == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out
-----------------------------------------------------------------------------
Init == /\ InChan!Init
        /\ OutChan!Init
        /\ q = <<>>
        
TypeInvariant == /\ InChan!TypeInvariant
                 /\ OutChan!TypeInvariant
                 /\ q \in Seq(Message)
                 
SSend(msg) == /\ InChan!Send(msg) \* Send msg on channel in.
              /\ UNCHANGED <<out, q>>
              
BufRcv == /\ InChan!Rcv             \* Receive message from channel in
          /\ q' = Append(q, in.val) \* and append it to tail of q.
          /\ UNCHANGED out
          
BufSend == /\ q # <<>>
           /\ OutChan!Send(Head(q))
           /\ q' = Tail(q)
           /\ UNCHANGED in
           
RRcv == /\ OutChan!Rcv
        /\ UNCHANGED <<in, q>>
        
Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/RRcv
        
Spec == Init /\ [][Next]_<<in, out, q>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Fri Feb 07 17:15:13 GMT 2025 by gustavo.franke
\* Created Fri Feb 07 17:03:36 GMT 2025 by gustavo.franke
