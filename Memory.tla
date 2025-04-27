------------------------------- MODULE Memory -------------------------------
EXTENDS MemoryInterface
Inner(mem, ctl, buf) == INSTANCE InternalMemory

Spec == \EE mem, ctl, buf : Inner(mem, ctl, buf)!ISpec
=============================================================================
\* Modification History
\* Last modified Sun Apr 27 21:00:59 IST 2025 by gustavo.franke
\* Created Thu Feb 20 17:51:21 GMT 2025 by gustavo.franke
