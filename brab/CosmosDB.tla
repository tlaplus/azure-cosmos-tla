### Limitations Azure Cosmos Emulator:

- The emulator does not offer different Azure Cosmos DB consistency levels like the cloud service does.
- The emulator does not offer multi-region replication.

https://docs.microsoft.com/en-us/azure/cosmos-db/local-emulator?tabs=ssl-netstd21#differences-between-the-emulator-and-the-cloud-service

Limitations Azure Cosmos Linux Emulator:

- While consistency levels can be adjusted using command-line arguments for testing scenarios only (default setting is Session), a user might not expect the same behavior as in the cloud service. For instance, Strong and Bounded staleness consistency has no effect on the emulator, other than signaling to the Cosmos DB SDK the default consistency of the account.
- The Linux emulator does not offer multi-region replication.

https://docs.microsoft.com/en-us/azure/cosmos-db/linux-emulator?tabs=ssl-netstd21

### Candidate features to support:

- Optimistic Concurrency Control (OCC)
- if-match & _etag
- if-none-match

- Strong consistency
- Session Consistency
- Eventual Consistency
- Bounded Staleness
- Consistent Prefix

- relaxing consistency levels on a per-request basis

- multi-region writes & conflict feed
https://docs.microsoft.com/en-us/azure/cosmos-db/sql/database-transactions-optimistic-concurrency

- multiple documents/partition key (logical/physical partitions)
https://docs.microsoft.com/en-us/azure/cosmos-db/partitioning-overview

- cross-partition queries
https://docs.microsoft.com/en-us/azure/cosmos-db/sql/how-to-query-container#avoiding-cross-partition-queries

- stored procedures/triggers/UDFs
https://docs.microsoft.com/en-us/azure/cosmos-db/sql/stored-procedures-triggers-udfs

### Supported features:

- multiple regions (but only one write region)
- partition replica set (each region has a replica set)

- if-match & _etag

- Strong consistency
- Session Consistency (point reads within a partition)
- Eventual Consistency

- Partition keys & multiple LSNs?


----- MODULE CosmosDB ----
EXTENDS Integers, TLC, Sequences, SequencesExt, Bags, BagsExt, Functions

CONSTANT Regions

CONSTANT WriteRegions

CONSTANT Null, Data

--------------------------------------------------------------------------------

CONSTANT Clients
 
VARIABLE
    \* Null or the last response received by each client.
    client, 
    \* Program counter of the clients.
    pc,
    \* A session token that is shared (synced) between all clients.
    session
cvars == << client, pc, session >>
   
--------------------------------------------------------------------------------

INSTANCE CosmosMessages

VARIABLE
    outbox,
    \* A bag (multiset) of requests.
    inbox,
    \* A sequence of requests, which is essentially the Write-Ahead log of Cosmos DB.
    \* Since we don't care about an efficient implementation of Cosmos DB, we never
    \* checkpoint/apply and discard a prefix of the WAL.  Discarding the WAL, however,
    \* could be an optimization to speed-up model-checking by applying a prefix of the WAL
    \* into a "db entry".
    database
dvars == << outbox, inbox, database >>

CTypeOK ==
    \* Cosmos
    /\ outbox \in [ Clients -> Seq(Response) ]
    /\ DOMAIN inbox \subseteq Request
    /\ IsABag(inbox)
    /\ database \in Seq(Request)

\* TODO: The LastLSN doesn *not* take the document name into account!!!
\* TODO: => Is the LSN per database or per doc (collection)???
\* TODO:    If LSN not per database, the write response cannot do Len(db)+1 below!!!
\* TODO: => As per last paragraph of https://stackoverflow.com/a/71400260/6291195,
\* TODO:    the scope of a session token is a partition key and not a collection or database.

LastLSN ==
    CHOOSE i \in 1..Len(database):
            /\ database[i].type = "Write"
            /\ \A j \in (i+1)..Len(database): database[j].type # "Write"

LastData(doc) ==
    \* Null or the data of the last write.
    IF \E w \in Range(database): w.type = "Write" /\ w.doc = doc
    THEN database[LastLSN].data
    ELSE Null

ReadStrongResponse(request) ==
    {CError(request)} \cup 
        IF \E w \in Range(database): w.type = "Write" /\ w.doc = request.doc
        THEN {CReply(request, LastData(request.doc), LastLSN)}
        ELSE {} \* 404 in Cosmos DB

ReadSessionResponse(request) ==
    {CError(request)} \cup 
        \* {} models 404 in Cosmos DB
        LET InRange == { database[i] : i \in request.consistency.lsn..Len(database) }
            WritesInRange == { w \in InRange : w.type = "Write" /\ w.doc = request.doc }
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
        IF request.old = Null \/ request.old = LastData(request.doc)
        \* Can't use LastData' and Len(database') here bc database' not yet
        \* defined when TLC evaluates this expr. :-(
        THEN {CAck(request, request.data, Len(database) + 1)}
        ELSE {CNack(request, LastData(request.doc), Len(database))}

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
          \* TODO: a spec bug?  Perhaps, we can remove the WriteRegions
          \* TODO: CONSTANT?
          /\ req.region \in WriteRegions
          /\ \E res \in WriteResponse(req):
                    /\ IF res.type = "ACK" 
                       THEN database' = Append(database, req)
                       ELSE UNCHANGED database
                    /\ \/ outbox' = [outbox EXCEPT ![req.orig] = Append(@, res)]
                        \* TODO: When modeling request timeouts by having cosmos
                        \* TODO: add an error response into the client's inbox,
                        \* TODO: we cannot leave the client client's inbox (cosmos'
                        \* TODO: outbox) unchanged.  Instead, we have to non-det
                        \* TODO: Add error reponses here (see comment 9bywrkb6).
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
    \* TODO: 9bywrkb6
    \* TODO: After what time does a lost request time out at the client 
    \* TODO: (no, we don't want to model time explicitly)?
    \* TODO: For now, we subsume timeouts under the Error reponse, that
    \* TODO: leaves cosmos' state (dvars) unchanged.  The more interesting
    \* TODO: failure is a lost response (because cosmos' state changes).
    \* TODO: Lost responses are modeled in the CosmosRead and CosmosWrite
    \* TODO: actions.
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
    /\ CTypeOK

--------------------------------------------------------------------------------

CInit ==
    /\ client = [ c \in Clients |-> Null ]
    /\ outbox = [ c \in Clients |-> <<>> ]
    /\ inbox = <<>>
    \* Initially, the database is modeled to be not-empty, but to contain some
    \* data.
    /\ database \in [ {1} -> 
                        [
                            consistency: {[level |-> "Strong", lsn |-> 1]}, 
                            data: {1}, doc: {"doc1"}, old: {Null}, 
                            orig: Clients, region: Regions, type: {"Write"}
                        ]
                    ]


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
    /\ CInit
    /\ session = 1
    /\ pc = [ c \in Clients |-> "read" ]

Next ==
    \* Client actions
    \/ Workflow
    \* Cosmos actions
    \/ Cosmos

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Workflow)
    \* Assert that the variable outbox eventually changes, i.e., a database response
    \* is eventually send to clients.
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

SessionMonotonic ==
    \* In this spec, the session token is shared between all clients. The spec
    \* doesn't model how the session token is kept in sync. At any rate, it 
    \* is monotonic.
    [][session' > session]_session

================================================================================


Random material:

- https://www.youtube.com/watch?v=-4FsGysVD14