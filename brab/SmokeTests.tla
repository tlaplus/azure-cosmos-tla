----- MODULE SmokeTests -----
EXTENDS TLC, Naturals

\* StopAfter  has to be configured as a state constraint. It stops TLC after ~1
\* second or after generating 100 traces, whatever comes first, unless TLC
\* encountered an error.  In this case,  StopAfter  has no relevance.
StopAfter ==
    TLCGet("config").mode = "simulate" =>
    (* The smoke test has a time budget of 1 second. *)
    \/ TLCSet("exit", TLCGet("duration") > 1)
    (* Generating 100 traces should provide reasonable coverage. *)
    \/ TLCSet("exit", TLCGet("diameter") > 99)


====