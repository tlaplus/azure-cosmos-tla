----- MODULE CosmosDB ----
EXTENDS Integers, TLC, Sequences, SequencesExt, Bags, BagsExt, Functions

CONSTANT Data, Null

Levels ==
    {"Strong", "Bounded_staleness", "Session", "Consistent_prefix", "Eventual"}

Consistency ==
    [level: Levels, lsn: Int] \* log-sequence-number (lsn)

CONSTANT Regions

CONSTANT WriteRegions
    
--------------------------------------------------------------------------------

CONSTANT Clients
 
VARIABLE client, pc
cvars == << client, pc >>
   
--------------------------------------------------------------------------------

\* Request: Client -> Cosmos
Request ==
    [
        doc: STRING,     \* The document that was read.
        \* data: Data,      \* The data that was read.
        type: {"Read"}, 
        consistency: Consistency, 
        region: Regions, \* The region the original read request was sent to.
        orig: Clients    \* The client that originally sent the read request.
    ] \cup
    [
        doc: STRING,     \* The document that was written.
        data: Data,      \* The data that was written.
        old: Data \cup {Null},    \* If not Null, the expected data to be overriden (If-Match).  Note that If-Match & etags are essentially compare-and-swap.
        type: {"Write"}, 
        consistency: Consistency, 
        region: WriteRegions, \* The region the original write request was sent to.
        orig: Clients
    ]

\* Response: Cosmos -> Client
Response ==
    [
        doc: STRING,     \* The document that was written.
        data: Data,    \* "ACK", a session token, or the data that was read.
        type: {"Reply", "Error"}, 
        consistency: Consistency, 
        region: Regions, \* The region the original read request was sent to.
        orig: {"cosmos"}
    ] \cup 
    [
        doc: STRING,       \* The document that was written.
        data: Data \cup {Null},      \* Non-null if NACK because of If-Match.
        \* In case of error, the write might or might not have succeeded. An error
        \* models the case that the database response to a write request was lost.
        \* Message duplications is assumed to be prevented by the communicaion
        \* protocol (e.g. TCP).
        type: {"ACK", "NACK", "Error"},
        consistency: Consistency, 
        region: WriteRegions, \* The region the original read request was sent to.
        orig: {"cosmos"}
    ]

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
    LET error == [
            doc |-> request.doc,
            data |-> Null,
            type |-> "Error",
            consistency |-> [level |-> request.consistency.level, lsn |-> -1],
            region |-> request.region,
            orig |-> "cosmos"
        ]
        reply(data, lsn) == [
            doc |-> request.doc,
            data |-> data,
            type |-> "Reply",
            consistency |-> [level |-> request.consistency.level, lsn |-> lsn],
            region |-> request.region,
            orig |-> "cosmos"
        ]
    IN {error} \cup 
        IF \E w \in Range(database): w.type = "Write"
        THEN {reply(LastData, LastLSN)}
        ELSE {} \* 404 in Cosmos DB


ReadResponse(request) ==
    CASE request.consistency.level = "Strong" -> ReadStrongResponse(request)
        [] request.consistency.level = "Bounded_staleness" -> {}
        [] request.consistency.level = "Session" -> {}
        [] request.consistency.level = "Consistent_prefix" -> {}
        [] request.consistency.level = "Eventual" -> {}

WriteStrongResponse(request) ==
    \* With strong consistency, any previous (happen-before) write to any region has
    \* succeeded and is fully replicated.
    LET error == [
            doc |-> request.doc,
            data |-> Null,
            type |-> "Error",
            consistency |-> [level |-> request.consistency.level, lsn |-> -1],
            region |-> request.region,
            orig |-> "cosmos"
        ]
        ack == [
            doc |-> request.doc,
            data |-> Null,
            type |-> "ACK",
            consistency |-> [level |-> request.consistency.level, lsn |-> Len(database) + 1], \* lsn is length of DB \* Can't do Len(database') here bc database' not yet defined when TLC evaluates this expr.
            region |-> request.region,
            orig |-> "cosmos"
        ]
        nack(d) == [
            doc |-> request.doc,
            data |-> d,
            type |-> "NACK",
            consistency |-> [level |-> request.consistency.level, lsn |-> Len(database)],
            region |-> request.region,
            orig |-> "cosmos"
        ]
    IN {error} \cup 
        IF request.old = Null \/ request.old = LastData
        THEN {ack}
        ELSE {nack(LastData)}

WriteResponse(request) ==
    \* TODO: Dependeing on the consistency level, the write might not be enabled
    \* TODO: if old (if-match) is part of the request.  For example, client c1
    \* TODO: might write in region A followed by c2 writing in region B with an
    \* TODO: if-match of c1's write.  Under strong and session consistency, this
    \* TODO: is easy bc we can assume that c1's write has been replicated. Under
    \* TODO: eventual consistency we cannot assume that c1's write has been replicated.
    \* TODO: In this case, the write has to be delayed, fail, or succeed.
    CASE request.consistency.level = "Strong" -> WriteStrongResponse(request)
        [] request.consistency.level = "Bounded_staleness" -> {}
        [] request.consistency.level = "Session" -> {}
        [] request.consistency.level = "Consistent_prefix" -> {}
        [] request.consistency.level = "Eventual" -> {}

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
                       \/ UNCHANGED <<outbox>> \* Response is lost.
          /\ inbox' = BagRemove(inbox, req)
          /\ UNCHANGED cvars

CosmosRead ==
    \E req \in DOMAIN inbox:
        /\ req.type = "Read"
        /\ database' = Append(database, req)
        /\ \/ \E res \in ReadResponse(req):
                outbox' = [outbox EXCEPT ![req.orig] = Append(@, res)]
           \/ UNCHANGED outbox \* Response is lost.
        /\ inbox' = BagRemove(inbox, req)
        /\ UNCHANGED cvars

CosmosLose ==
    \* Loose the request.
    \E req \in DOMAIN inbox:
        /\ inbox' = BagRemove(inbox, req)
        /\ UNCHANGED <<cvars, database, outbox>>

Cosmos ==
    \/ CosmosLose
    \/ CosmosRead
    \/ CosmosWrite

--------------------------------------------------------------------------------

vars == <<cvars, dvars>>

TypeOK ==
    \* Clients
    /\ DOMAIN pc = Clients
    /\ Range(pc) \subseteq {"start", "write", "retry", "read", "receive", "error"}
    /\ client \in [Clients -> (Response \cup {Null})]
    \* Cosmos
    /\ outbox \in [ Clients -> Seq(Response) ]
    /\ IsABag(inbox)
    /\ DOMAIN inbox \subseteq Request
    /\ database \in Seq(Request)

--------------------------------------------------------------------------------

InitialRequest ==
    /\ \E c \in Clients :
        \* start -> receive
        /\ pc[c] = "start"
        /\ pc' = [ pc EXCEPT ![c] = "receive" ]
        /\ LET req == [
                doc |-> "doc1",
                data |-> c,
                old |-> Null,
                type |-> "Write",
                \* TODO This will issue two writes with the same lsn. Not sure if this is an issue?!
                consistency |-> [level |-> "Strong", lsn |-> -1],
                region |-> "R",
                orig |-> c
               ]   
           IN /\ inbox' = BagAdd(inbox, req)
    /\ UNCHANGED <<database, outbox, client>>
    

SendWriteRequest ==
    /\ UNCHANGED client
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
                data |-> IF res.data # Null THEN res.data \o c ELSE c,
                old |-> Null,
                type |-> "Write",
                consistency |-> res.consistency,
                region |-> res.region,
                orig |-> c
               ]   
               IN /\ inbox' = BagAdd(inbox, req)
                  /\ UNCHANGED <<database, outbox>>

SendReadRequest ==
    /\ UNCHANGED client
    /\ \E c \in Clients :
        \* send -> receive
        /\ pc[c] = "read"
        /\ pc' = [ pc EXCEPT ![c] = "receive" ]
        \* A client can send a request unless it has a response pending.
        /\ outbox[c] = <<>>
        \* Given a prior response, a client can send a request.
        /\ client[c] # Null
        /\ LET res == client[c] IN
            /\ LET req == [
                doc |-> res.doc,
                type |-> "Read",
                consistency |-> res.consistency,
                region |-> res.region,
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
                   \/ /\ client'[c].type \in {"NACK"}
                      /\ pc' = [ pc EXCEPT ![c] = "retry" ]
                   \/ /\ client'[c].type \in {"Reply"}
                      /\ pc' = [ pc EXCEPT ![c] = "write" ]
                   \/ /\ client'[c].type \in {"Error"}
                      /\ pc' = [ pc EXCEPT ![c] = "error" ]
           ELSE UNCHANGED <<outbox, pc, client>>
    /\ UNCHANGED <<database, inbox>>

Workflow ==
    \/ InitialRequest
    \/ SendWriteRequest
    \/ SendReadRequest
    \/ ReceiveResponse
    
--------------------------------------------------------------------------------

Init ==
    /\ pc = [ c \in Clients |-> "start" ]
    /\ client = [ c \in Clients |-> Null ]
    /\ outbox = [ c \in Clients |-> <<>> ]
    /\ inbox = <<>>
    /\ database = <<>>

Next ==
    \* Client actions
    \/ Workflow
    \* Cosmos actions
    \/ Cosmos

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

Monotonic ==
    \* The (log of the) database only ever grows.
    [][Len(database') >= Len(database)]_vars

THEOREM Spec => Monotonic

================================================================================