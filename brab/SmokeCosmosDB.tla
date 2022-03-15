---- MODULE SmokeCosmosDB -----
EXTENDS MCCosmosDB

\* StopAfter  has to be configured as a state constraint. It stops TLC after ~1
\* second or after generating 100 traces, whatever comes first, unless TLC
\* encountered an error.  In this case,  StopAfter  has no relevance.
StopAfter ==
    TLCGet("config").mode = "simulate" =>
    (* The smoke test has a time budget of 1 second. *)
    \/ TLCSet("exit", TLCGet("duration") > 1)
    (* Generating 100 traces should provide reasonable coverage. *)
    \/ TLCSet("exit", TLCGet("diameter") > 99)

\* Test:
\* a) Writes 

TestNext ==
    /\ UNCHANGED <<cvars, dvars>>
    /\ LET request == [
                doc |-> "doc1",
                data |-> "a",
                old |-> Null,
                type |-> "Write",
                consistency |-> [level |-> "Strong", lsn |-> 0],
                region |-> "R",
                orig |-> "c1"
               ]
           IN LET responses == WriteResponse(request)
              IN \A res \in responses:
                    /\ res \in Response
                    /\ res.doc = "doc1"
                    /\ res.data = Null
                    /\ res.type \in {"ACK", "Error"}
                    /\ res.type = "ACK" => res.consistency = [level |-> "Strong",lsn |-> 1]
                    /\ res.type = "Error" => res.consistency = [level |-> "Strong",lsn |-> -1]
                    /\ res.region = "R"
                    /\ res.orig = "cosmos"
    /\ LET request == [
                doc |-> "doc1",
                data |-> "a",
                old |-> "a",
                type |-> "Write",
                consistency |-> [level |-> "Strong", lsn |-> 0],
                region |-> "R",
                orig |-> "c1"
               ]
           IN LET responses == WriteResponse(request)
              IN \A res \in responses:
                    /\ res \in Response
                    /\ res.doc = "doc1"
                    /\ res.type \in {"NACK", "Error"}
                    /\ res.type = "NACK" => 
                            /\ res.consistency = [level |-> "Strong",lsn |-> 0]
                            /\ res.data = Null
                    /\ res.type = "Error" =>
                            /\ res.consistency = [level |-> "Strong",lsn |-> -1]
                            /\ res.data = Null
                    /\ res.region = "R"
                    /\ res.orig = "cosmos"

======