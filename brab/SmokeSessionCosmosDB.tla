---- MODULE SmokeSessionCosmosDB -----
EXTENDS MCCosmosDB, FiniteSets, SmokeTests

\* This is a read for a token whose corresponding write might or might not yet have replicated
\* from region R to S.  If the write has already replicated, we return the value.  Since non-det
\* models the case that other processes make process, the behavior where the process issueing
\* the read waits is implicitly modeled.
\* TODO: unsynced returns a response such as "wait" that causes the CosmosRead action to leave
\* TODO: all varaibles unchanged.  However, if there is a read in database that tells us that 
\* TODO: Cosmos already returned the value previously, we don't have to add the wait to the response.
\* TODO: => Monotonic Reads

\* TODO: Session consistency cannot be tests at the level of ReadResponse but on the level of
\* TODO: CosmosReads.  We can stick the read request in Cosmos's inbox variable in the Init
\* TODO: predicate and then assert that all successor states are accounted for.


(*

A read with session consistency in region  S  and (session) token  t  whose corresponding write
happened in region  R  gives rise to the following TLA+ behaviors:

- If the write has already replicated from region  R  to region S  , the read in region  S  
  returns the value.

- If the write has not replicated from region  R  to region S  , the read in region  S  blocks/waits
  until the write has replicated from region  R  to region S  .  From the perspective of the process
  issuing the read in region  S  , it is blocked. However, other processes make progress.  We could make
  this explicit by defining  ReadSessionResponse  to equal a set that contains a block/wait response
  that causes  CosmosRead  to leave the variables unchanged.

*)

\* ?: Does a read with session consistency return a newer session token?  If not, the spec cannot rely 
 \* ?: on the client to include a newer token with a subsequent read, in which case  CosmosRead  has to 
 \* ?: make sure that the client gets monotonic reads by looking at the previous reads in the database
 \* ?: variable.
 \* ?: Suppose the following schedule: 
 \*    <<write, data=42, token=1, client=1>>
 \*    <<write, data=23, token=2, client=1>>
 \*    <<read, token=1, client=2>> \* session token lags behind.
 \*    The read can either return 42 or 23.  However, if it returns 23, does the response also contain token=2
 \* Yes, the read of client 2 with token 1 can return token 2 with data 23 if the database has managed to replicate.

\* We have to model session consistency s.t. the read in region  S  blocks/waits until the write in region  R because
\* there front-end specification could mutate its state.  In other words, we don't specify UNCHANGED vars but only
\* UNCHANGED <<database, ...>>

-----

\*    <<write, data=42, token=1, client=1>>
\*    <<write, data=23, token=1, client=2>>  => 42, 23 or 23, 42



\* In session consistency, within a single client session reads are guaranteed to honor:
\* - consistent-prefix (a prefix of the writes in the session)
\* - monotonic reads   (stale reads but reads cannot go backwards)
\* - monotonic writes  ()
\* - read-your-writes
\* - write-follows-reads
\* This assumes a single "writer" session or sharing the session token for multiple writers.

\* For an up-to-date session token, session consistency provides strong consistency.  For a stale session tokens, the client
\* gets consistent prefix according to the CosmosDB documentation.  All bets seem off when multi-region writes come into the
\* picture.  At this stage, if-match & etags do not work on conflict resolution has to be employed.  The default conflicht
\* resolution is last write wins (LWW) where the "synchronized" clocks of the distributed system are used to determine the 
\* last write (https://docs.microsoft.com/en-us/azure/cosmos-db/conflict-resolution-policies).

\* "blind writes" 


\* Careful: The session token is per partition key.  If a query spans multiple partitions, the session token does not
\* quarantee session consistency, but only consistent prefix consistency (https://stackoverflow.com/a/71400260/6291195).
TestInit ==
    /\ session = 1
    /\ pc = [ c \in Clients |-> "read" ]
    /\ client = [ c \in Clients |-> Null ]
    /\ outbox = [ c \in Clients |-> <<>> ]
    /\ \/ /\ LET req == CRead("doc1", [level |-> "Session", lsn |-> 1], "R", 1)
             IN inbox \in [ {req} -> {1} ]
          /\ database = <<[ consistency |-> [level |-> "Strong", lsn |-> 1], 
                            data |-> 1, doc |-> "doc1", old |-> Null, 
                            orig |-> 1, region |-> "R", type |-> "Write" ]>>
       \/ /\ LET req == CRead("doc1", [level |-> "Session", lsn |-> 1], "R", 1)
             IN inbox \in [ {req} -> {1} ]
          /\ database = <<[ consistency |-> [level |-> "Strong", lsn |-> 1], 
                            data |-> 1, doc |-> "doc1", old |-> Null, 
                            orig |-> 1, region |-> "R", type |-> "Write" ]>>

TestNext ==
    /\ UNCHANGED <<cvars>>
    /\ CosmosRead

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

====
    \* Read|Session|No If-Match|Region A|latest token
    \* This is just an ordinary read that gets the latest value.
    /\ LET responses == ReadResponse(CRead("doc1", [level |-> "Session", lsn |-> 1], "R", "c1"))
       IN /\ Cardinality(responses) = 2
          /\ \A res \in responses:
                /\ res \in Response
                /\ res.doc = "doc1"
                /\ res.type \in {"Reply", "Error"}
                /\ res.type = "Reply" => 
                        /\ res.consistency = [level |-> "Session",lsn |-> 1]
                        /\ res.data = 1
                /\ res.type = "Error" =>
                        /\ res.consistency = [level |-> "Session", lsn |-> -1]
                        /\ res.data = Null
                /\ res.region = "R"
                /\ res.orig = "cosmos"
    \* Read|Session|No If-Match|Region A|newer token
    \* This is a read for a newer token.
    /\ LET responses == ReadResponse(CRead("doc1", [level |-> "Session", lsn |-> 2], "R", "c1"))
       IN /\ Cardinality(responses) = 1
          /\ \A res \in responses:
                /\ res \in Response
                /\ res.doc = "doc1"
                /\ res.type \in {"Error"}
                /\ res.type = "Error" =>
                        /\ res.consistency = [level |-> "Session", lsn |-> -1]
                        /\ res.data = Null
                /\ res.region = "R"
                /\ res.orig = "cosmos"
    \* 1. Read|Session|No If-Match|Region B|latest token
    /\ LET responses == ReadResponse(CRead("doc1", [level |-> "Session", lsn |-> 1], "S", "c1"))
       IN /\ Cardinality(responses) = 2
          /\ \A res \in responses:
                /\ res \in Response
                /\ res.doc = "doc1"
                /\ res.type \in {"Replay", "Error"}
                /\ res.type = "Error" =>
                        /\ res.consistency = [level |-> "Session", lsn |-> -1]
                        /\ res.data = Null
                /\ res.region = "R"
                /\ res.orig = "cosmos"
    \* 2. Read|Session|No If-Match|Region B|latest token

======