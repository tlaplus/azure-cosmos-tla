----- MODULE CosmosDB ----
EXTENDS Integers, TLC, Sequences, SequencesExt, Bags, BagsExt, Functions

CONSTANT Regions

CONSTANT WriteRegions

CONSTANT Null, Data

--------------------------------------------------------------------------------

CONSTANT Clients
 
VARIABLE client, pc, session
cvars == << client, pc, session >>
   
--------------------------------------------------------------------------------

INSTANCE CosmosMessages

VARIABLE
    outbox,
    \* A bag (multiset) of requests.
    inbox,
    \* A sequence of requests.
    database
dvars == << outbox, inbox, database >>

LastLSN ==
    CHOOSE i \in 1..Len(database):
                    /\ database[i].type = "Write"
                    /\ \A j \in (i+1)..Len(database): database[j].type # "Write"

LastData ==
    \* Null or the data of the last write.
    IF \E w \in Range(database): w.type = "Write"
    THEN database[LastLSN].data
    ELSE Null

ReadStrongResponse(request) ==
    {CError(request)} \cup 
        IF \E w \in Range(database): w.type = "Write"
        THEN {CReply(request, LastData, LastLSN)}
        ELSE {} \* 404 in Cosmos DB

ReadSessionResponse(request) ==
    {CError(request)} \cup 
        \* {} models 404 in Cosmos DB
        LET InRange == { database[i] : i \in request.consistency.lsn..Len(database) }
            WritesInRange == { w \in InRange : w.type = "Write" }
        IN { CReply(request, w.data, w.consistency.lsn) : w \in WritesInRange }

ReadEventualResponse(request) ==
    FALSE \* TODO

ReadResponse(request) ==
    CASE request.consistency.level = "Strong" -> ReadStrongResponse(request)
        [] request.consistency.level = "Bounded_staleness" -> FALSE \* TODO
        [] request.consistency.level = "Session" -> ReadSessionResponse(request)
        [] request.consistency.level = "Consistent_prefix" -> FALSE \* TODO
        [] request.consistency.level = "Eventual" -> ReadEventualResponse(request)

WriteStrongResponse(request) ==
    \* With strong consistency, any previous (happen-before) write to any region has
    \* succeeded and is fully replicated.
    {CError(request)} \cup 
        IF request.old = Null \/ request.old = LastData
        \* lsn is length of DB \* Can't do Len(database') here bc database' not yet
        \* defined when TLC evaluates this expr.
        THEN {CAck(request, Len(database) + 1)}
        ELSE {CNack(request, LastData, Len(database))}

 WriteSessionResponse(request) ==
     WriteStrongResponse(request)

WriteResponse(request) ==
    \* TODO: Dependeing on the consistency level, the write might not be enabled
    \* TODO: if old (if-match) is part of the request.  For example, client c1
    \* TODO: might write in region A followed by c2 writing in region B with an
    \* TODO: if-match of c1's write.  Under strong and session consistency, this
    \* TODO: is easy bc we can assume that c1's write has been replicated. Under
    \* TODO: eventual consistency we cannot assume that c1's write has been replicated.
    \* TODO: In this case, the write has to be delayed, fail, or succeed.
    CASE request.consistency.level = "Strong" -> WriteStrongResponse(request)
        [] request.consistency.level = "Bounded_staleness" -> FALSE \* TODO
        [] request.consistency.level = "Session" -> WriteSessionResponse(request)
        [] request.consistency.level = "Consistent_prefix" -> FALSE \* TODO
        [] request.consistency.level = "Eventual" -> FALSE \* TODO

CosmosWrite ==
    \E req \in DOMAIN inbox:
          /\ req.type = "Write"
          \* TODO: Should this rather raise an error because it indicates
          \* TODO: a spec bug?
          /\ req.region \in WriteRegions
          /\ \E res \in WriteResponse(req):
                    /\ IF res.type = "ACK" 
                       THEN database' = Append(database, req)
                       ELSE UNCHANGED database
                    /\ \/ outbox' = [outbox EXCEPT ![req.orig] = Append(@, res)]
                    \*    \/ UNCHANGED <<outbox>> \* Response is lost.
          /\ inbox' = BagRemove(inbox, req)
          /\ UNCHANGED cvars

CosmosRead ==
    \E req \in DOMAIN inbox:
        /\ req.type = "Read"
        /\ database' = Append(database, req)
        /\ \/ \E res \in ReadResponse(req):
                outbox' = [outbox EXCEPT ![req.orig] = Append(@, res)]
        \*    \/ UNCHANGED outbox \* Response is lost.
        /\ inbox' = BagRemove(inbox, req)
        /\ UNCHANGED cvars

CosmosLose ==
    \* Loose the request.
    \E req \in DOMAIN inbox:
        /\ inbox' = BagRemove(inbox, req)
        /\ UNCHANGED <<cvars, database, outbox>>

Cosmos ==
    \* \/ CosmosLose
    \/ CosmosRead
    \/ CosmosWrite

--------------------------------------------------------------------------------

vars == <<cvars, dvars>>

TypeOK ==
    \* Clients
    /\ DOMAIN pc = Clients
    /\ Range(pc) \subseteq {"start", "write", "retry", "read", "receive", "error", "done"}
    /\ client \in [Clients -> (Response \cup {Null})]
    \* Cosmos
    /\ outbox \in [ Clients -> Seq(Response) ]
    /\ IsABag(inbox)
    /\ DOMAIN inbox \subseteq Request
    /\ database \in Seq(Request)

--------------------------------------------------------------------------------

SendWriteRequest ==
    /\ UNCHANGED <<client, session>>
    /\ \E c \in Clients :
        \* send -> receive
        /\ pc[c] = "write"
        /\ pc' = [ pc EXCEPT ![c] = "receive" ]
        \* A client can send a request unless it has a response pending.
        /\ outbox[c] = <<>>
        \* Given a prior response, a client can send a request.
        /\ client[c] # Null
        /\ LET res == client[c] IN
            /\ LET req == [
                doc |-> res.doc,
                data |-> IF res.data # Null THEN res.data + c ELSE c,
                old |-> Null, \* No if-match for now.
                \* old |-> res.data,
                type |-> "Write",
                consistency |-> res.consistency,
                region |-> res.region,
                orig |-> c
               ]   
               IN /\ inbox' = BagAdd(inbox, req)
                  /\ UNCHANGED <<database, outbox>>

SendReadRequest ==
    /\ UNCHANGED <<client, session>>
    /\ \E c \in Clients :
        \* send -> receive
        /\ pc[c] = "read"
        /\ pc' = [ pc EXCEPT ![c] = "receive" ]
        \* A client can send a request unless it has a response pending.
        /\ outbox[c] = <<>>
        /\ LET req == [
            doc |-> "doc1",
            type |-> "Read",
            consistency |-> [level |-> "Session", lsn |-> session],
            \* consistency |-> IF client[c] # Null 
            \*                 THEN client[c].consistency
            \*                 ELSE [level |-> "Session", lsn |-> 1],
            region |-> "R",
            orig |-> c
           ]   
           IN /\ inbox' = BagAdd(inbox, req)
              /\ UNCHANGED <<database, outbox>>

ReceiveResponse ==
    \* TODO: This action could be squashed into read, write, error, ...
    \* TODO: because it just "moves" the response from the outbox to
    \* TODO: the client variable and updates the pc variable.
    /\ \E c \in Clients :
        /\ pc[c] = "receive"
        /\ IF outbox[c] # <<>>
           THEN /\ outbox' = [outbox EXCEPT ![c] = Tail(@)]
                /\ client' = [ client EXCEPT ![c] = Head(outbox[c]) ]
                /\ \/ /\ client'[c].type \in {"ACK"}
                      /\ pc' = [ pc EXCEPT ![c] = "read" ]
                      /\ session' = client'[c].consistency.lsn
                   \/ /\ client'[c].type \in {"NACK"}
                      /\ pc' = [ pc EXCEPT ![c] = "retry" ]
                      /\ UNCHANGED session
                   \/ /\ client'[c].type \in {"Reply"}
                      /\ pc' = [ pc EXCEPT ![c] = "write" ]
                      /\ UNCHANGED session
                   \/ /\ client'[c].type \in {"Error"}
                      /\ pc' = [ pc EXCEPT ![c] = "error" ]
                      /\ UNCHANGED session
           ELSE UNCHANGED <<outbox, pc, client, session>>
    /\ UNCHANGED <<database, inbox>>

HandleNack ==
    /\ \E c \in Clients :
        /\ pc[c] = "retry"
        \* Just trigger a rewrite because NACK response contains the
        \* data value at the time of the failed write.
        /\ pc' = [ pc EXCEPT ![c] = "write" ]
    /\ UNCHANGED <<dvars, client, session>>
    
HandleError ==
    /\ \E c \in Clients :
        /\ pc[c] = "error"
        \* TODO Do something meaningful here.  One possibility is to
        \* TODO assert that no behavior terminates in infinite stuttering
        \* TODO pc[c] = "error" for one or more clients:
        \* TODO   <>[](\A c \in Clients: pc[c] # "error")
        /\ pc' = [ pc EXCEPT ![c] = "done" ]
    /\ UNCHANGED <<dvars, client, session>>

Workflow ==
    \/ SendWriteRequest
    \/ SendReadRequest
    \/ ReceiveResponse
    \/ HandleNack
    \/ HandleError
    
--------------------------------------------------------------------------------

Init ==
    /\ session = 1
    /\ pc = [ c \in Clients |-> "read" ]
    /\ client = [ c \in Clients |-> Null ]
    /\ outbox = [ c \in Clients |-> <<>> ]
    /\ inbox = <<>>
    /\ database \in [ {1} -> 
                        [
                            consistency: {[level |-> "Strong", lsn |-> 1]}, 
                            data: {1}, doc: {"doc1"}, old: {Null}, 
                            orig: Clients, region: Regions, type: {"Write"}
                        ]
                    ]
Next ==
    \* Client actions
    \/ Workflow
    \* Cosmos actions
    \/ Cosmos

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Workflow)
    \* Assert that the variable outbox eventually changes that is a database response
    \* eventually is send to clients.
    /\ WF_outbox(CosmosRead)
    /\ WF_outbox(CosmosWrite)

Monotonic ==
    \* The (log of the) database only ever grows.
    [][Len(database') >= Len(database)]_vars

THEOREM Spec => Monotonic

LSNMontonic ==
    \* The LSN of write operations kept in variable are not monotonic!
    \A i,j \in DOMAIN database:
        (i < j /\ database[i].type = "Write" /\ database[j].type = "Write" )
        => database[i].consistency.lsn <= database[j].consistency.lsn


================================================================================