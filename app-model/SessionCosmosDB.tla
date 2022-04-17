---- MODULE SessionCosmosDB -----
EXTENDS MCCosmosDB, FiniteSets, SmokeTests

sessionRegions ==
    regions \cup {"S"}

TestInit ==
    /\ session = 1
    /\ pc = [ c \in Clients |-> "read" ]
    /\ client = [ c \in Clients |-> Null ]
    /\ outbox = [ c \in Clients |-> <<>> ]
    \* Write in region R which might or might not has been replicated to region S.
    \* Client in region S uses the up-to-date session token.
    /\ inbox \in [ {CRead("doc1", [level |-> "Session", lsn |-> 1], "S", 1)} -> {1} ]
    /\ database = <<[ consistency |-> [level |-> "Strong", lsn |-> 1], 
                      data |-> 1, doc |-> "doc1", old |-> Null, 
                      orig |-> 1, region |-> "R", type |-> "Write" ]>>

TestNext ==
    /\ UNCHANGED cvars
    /\ \/ CosmosRead
       \/ UNCHANGED vars

Invariant ==
    (TLCGet("level") = 2) =>
        ( 
            \* A) Assert the states
            /\  \* 2. database does not change and no response (case that replica is out of sync)
                \* \/ UNCHANGED <<inbox, database, outbox>>
                \* 1. database changes but response is lost
                \/ outbox[1] = <<>>
                \* 3. database changes and error response
                \/ /\ Len(database) = 2
                   /\ outbox[1][1].type = "Error"
                \* 4. database changes and regular reply
                \/ /\ Len(database) = 2
                   /\ outbox[1][1].type = "Reply"
            \* B) Assert the right number of states with TLCGet(...)
            \* /\ TLCGet("distinct") = 4
        )

======