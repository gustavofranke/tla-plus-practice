--------------------------- MODULE InternalMemory ---------------------------
(*
The processing of this request is represented by the following three steps:

| ctl[p] = "rdy" |           | ctl[p] = "busy" |
| buf [p] =...   |- Req(p) ->| buf [p] = req   |
| mem[a] =...    |           | mem[a] =...     |

          | ctl[p] = "done" |           | ctl[p] = "rdy"  |
- Do(p) ->| buf [p] = NoVal |- Rsp(p) ->| buf [p] = NoVal |
          | mem[a] = v      |           | mem[a] = v      |

*)
EXTENDS MemoryInterface
VARIABLES mem, ctl, buf

IInit ==
    /\ mem \in [Adr -> Val]
    /\ ctl = [p \in Proc |-> "rdy"]
    /\ buf = [p \in Proc |-> NoVal]
    /\ memInt \in InitMemInt
    
TypeInvariant ==
    /\ mem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
    /\ buf \in [Proc -> MReq \union Val \union {NoVal}]
    
Req(p) ==
    /\ ctl[p] = "rdy"
    /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
    /\ UNCHANGED mem
    /\ UNCHANGED memInt \* added by me
    
Do(p) ==
    /\ ctl[p] = "busy"
    /\ mem' = IF buf[p].op = "Wr"
              THEN [mem EXCEPT ![buf[p].adr] = buf[p].val]
              ELSE mem
    /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr" THEN NoVal ELSE mem[buf[p].adr]]
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ UNCHANGED memInt

Rsp(p) ==
    /\ ctl[p] = "done"
    /\ Reply(p, buf[p], memInt, memInt')
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ UNCHANGED <<mem, buf>>
    /\ UNCHANGED memInt \* added by me

INext == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

ISpec == IInit /\ [][INext]_<<memInt, mem, ctl, buf>>
-----------------------------------------------------------------------------
THEOREM ISpec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Fri Apr 25 21:55:09 IST 2025 by gustavo.franke
\* Created Thu Feb 20 17:31:39 GMT 2025 by gustavo.franke
