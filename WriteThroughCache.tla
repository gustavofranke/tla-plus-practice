------------------------- MODULE WriteThroughCache -------------------------
(*
                                                  ||
                                                  ||  bus
                                                  ||
                             |---------------|    ||
                             |  .--------.   |    ||
                             |  |cache[p]|<--+----||
                             |  '--------'   |    ||
                             |     |  ^      |    ||                 
                             |     v  |      |    ||                  .-------.
 .-------------.             |   .--------.  |    ||                  |       |
 | Processor p |<-- memInt --+-->| buf[p] |--+--->||                  |  wmem |
 '-------------'             |   '--------'  |    ||                  |       |
                             |               |    ||                  |       |
                             |   .--------.  |    ||                  |       |
                             |   | ctl[p] |  |    ||      .------.    |       |
                             |   '--------'  |    ||----->| memQ |--->|       |
                             |---------------|    ||      '------'    |       |
                                                  ||                  '-------'
                                                  ||
*)
EXTENDS Naturals, Sequences, MemoryInterface
VARIABLES wmem, ctl, buf, cache, memQ
CONSTANT QLen
ASSUME (QLen \in Nat) /\ (QLen > 0)
M == INSTANCE InternalMemory WITH mem <- wmem

-----------------------------------------------------------------------------

Init == \* The initial predicate
    /\ M!IInit \* wmem, buf, and ctl are initialised as in the internal memory spec.
    /\ cache = \* All caches are initially empty (cache[p][a] = NoVal for all p, a).
        [p \in Proc |-> [a \in Adr |-> NoVal]]
    /\ memQ = <<>> \* The queue memQ is initially empty.

TypeInvariant == \* the type invariant
    /\ wmem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"rdy", "busy", "waiting", "done"}]
    /\ buf \in [Proc -> MReq \union Val \union {NoVal}]
    /\ cache \in [Proc -> [Adr -> Val \union {NoVal}]]
    /\ memQ \in Seq(Proc \X MReq) \* memQ is a sequence of <proc, request> pairs.

Coherence == \* Asserts that if two processors' caches both have copies,
    \A p, q \in Proc, a \in Adr : \*  of an address, then those copies have equal values
     (NoVal \in {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

-----------------------------------------------------------------------------

Req(p) == \* Processor p issues a request
    M!Req(p) /\ UNCHANGED <<cache, memQ>>
    
Rsp(p) == \* The system issues a response to processor p.
    M!Rsp(p) /\ UNCHANGED <<cache, memQ>>

RdMiss(p) == \* Enqueue a request to write value from memory to p's cache.
    /\ (ctl[p] = "busy") /\ (buf[p].op = "Rd") \* Enabled on a read request when
    /\ cache[p][buf[p].adr] = NoVal \* the address is not in p's cache
    /\ Len(memQ) < QLen \* and memQ is not full.
    /\ memQ' = Append(memQ, <<p, buf[p]>>) \* Append <p, request> to memQ.
    /\ ctl' = [ctl EXCEPT ![p] = "waiting"] \* Set ctl[p] to "waiting".
    /\ UNCHANGED <<memInt, wmem, buf, cache>>
    
DoRd(p) == \* Perform a read by p of a value in its cache.
    /\ ctl[p] \in {"busy", "waiting"} \* Enabled if a read request is pending and address is in cache.
    /\ buf[p].op = "Rd"
    /\ cache[p][buf[p].adr] # NoVal
    /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]] \* Get Result from cache.
    /\ ctl' = [ctl EXCEPT ![p] = "done"] \* Set ctl[p] to "done".
    /\ UNCHANGED <<memInt, wmem, cache, memQ>>

DoWr(p) == \* Write to p's cache, update other caches, and enqueue memory update.
    LET r == buf[p] \* Processor p\s request.
    IN /\ (ctl[p] = "busy") /\ (r.op = "Wr") \* Enabled if write request pending and memQ is not full.
       /\ Len(memQ) < QLen
       /\ cache' = \* Update p's cache and any other cache that has a copy.
            [q \in Proc |-> IF (p = q) \/ (cache[q][r.adr] # NoVal)
                            THEN [cache[q] EXCEPT ![r.adr] = r.val]
                            ELSE cache[q]]
       /\ memQ' = Append(memQ, <<p, r>>) \* Enqueue write at tail of memQ.
       /\ buf' = [buf EXCEPT ![p] = NoVal] \* Generate response.
       /\ ctl' = [ctl EXCEPT ![p] = "done"] \* Set ctl to indicate request is done.
       /\ UNCHANGED <<memInt, wmem>>

vmem == \* The value wmem will have after all the writes in memQ are performed.
    LET f[i \in 0..Len(memQ)] == \* The value wmem will have after the first i writes in memQ are performed.
        IF i = 0 THEN wmem
                 ELSE IF memQ[i][2].op = "Rd"
                        THEN f[i - 1]
                        ELSE [f[i - 1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
    IN f[Len(memQ)]

MemQWr == \* Perform write at head of memQ to memory.
    LET r == Head(memQ)[2] \* The request at the head of memQ.
    IN /\ (memQ # <<>>) /\ (r.op = "Wr") \* Enabled if Head(memQ) a write.
       /\ wmem' = [wmem EXCEPT ![r.adr] = r.val] \* Perform the write to memory.
       /\ memQ' = Tail(memQ) \* Remove the write from memQ.
       /\ UNCHANGED <<memInt, buf, ctl, cache>>

MemQRd == \* Perform an enqueued read to memory.
    LET p == Head(memQ)[1] \* The requesting processor.
        r == Head(memQ)[2] \* The request at the head of memQ.
    IN /\ (memQ # <<>>) /\ (r.op = "Rd") \* Enabled if Head(memQ) is a read.
       /\ memQ' = Tail(memQ) \* Remove the head of memQ.
       /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]] \* Put value from memory or memQ in p's cache.
       /\ UNCHANGED <<memInt, wmem, buf, ctl>>

Evict(p, a) == \* Remove address a from p's cache.
    /\ (ctl[p] = "waiting") => (buf[p].adr # a) \* Can't evict a if it was just read into cache from memory.
    /\ cache' = [cache EXCEPT ![p][a] = NoVal]
    /\ UNCHANGED <<memInt, wmem, buf, ctl, memQ>>

Next == \/ \E p \in Proc : \/ Req(p) \/ Rsp(p)
                           \/ RdMiss(p) \/ DoRd(p)  \/ DoWr(p)
                           \/ \E a \in Adr : Evict(p, a)
        \/ MemQWr \/ MemQRd

Spec == Init /\ [][Next]_<<memInt, wmem, buf, ctl, cache, memQ>>
-----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ Coherence)
-----------------------------------------------------------------------------
LM == INSTANCE Memory \* The memory spec. with internal variables hidden.
THEOREM Spec => LM!Spec \* Formula Spec implements the memory spec.
=============================================================================
\* Modification History
\* Last modified Sun Apr 27 21:10:55 IST 2025 by gustavo.franke
\* Created Fri Feb 21 11:58:20 GMT 2025 by gustavo.franke
