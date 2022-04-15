---- MODULE MCCosmosDB_TTrace ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, MCCosmosDB

_expression ==
    LET MCCosmosDB_TEExpression == INSTANCE MCCosmosDB_TEExpression
    IN MCCosmosDB_TEExpression!expression
----

_trace ==
    LET MCCosmosDB_trace == INSTANCE MCCosmosDB_trace
    IN MCCosmosDB_trace!trace
----

_prop ==
    ~<>[](
        /\ database = (_trace[Len(_trace)].database)
        /\ pc = (_trace[Len(_trace)].pc)
        /\ session = (_trace[Len(_trace)].session)
        /\ client = (_trace[Len(_trace)].client)
        /\ outbox = (_trace[Len(_trace)].outbox)
        /\ inbox = (_trace[Len(_trace)].inbox)
    )
----

_init ==
    /\ database = _trace[1].database
    /\ pc = _trace[1].pc
    /\ outbox = _trace[1].outbox
    /\ session = _trace[1].session
    /\ client = _trace[1].client
    /\ inbox = _trace[1].inbox
----

_next ==
    /\ \E i,j \in DOMAIN _trace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ database  = _trace[i].database
        /\ database' = _trace[j].database
        /\ pc  = _trace[i].pc
        /\ pc' = _trace[j].pc
        /\ outbox  = _trace[i].outbox
        /\ outbox' = _trace[j].outbox
        /\ session  = _trace[i].session
        /\ session' = _trace[j].session
        /\ client  = _trace[i].client
        /\ client' = _trace[j].client
        /\ inbox  = _trace[i].inbox
        /\ inbox' = _trace[j].inbox

HL == INSTANCE MCCosmosDB
_implements == 
    HL!Init /\ [][HL!Next]_HL!vars

=============================================================================

---- MODULE MCCosmosDB_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, MCCosmosDB

expression == 
    [
        database |-> database
        ,pc |-> pc
        ,outbox |-> outbox
        ,session |-> session
        ,client |-> client
        ,inbox |-> inbox
    ]

=============================================================================

---- MODULE MCCosmosDB_trace ----
EXTENDS TLC, MCCosmosDB

trace == 
    <<
    ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"read", "read">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> <<>>]),
    ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"read", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 2] :> 1)]),
    ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"read", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> << >>]),
    ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"receive", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1] :> 1)]),
    ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"receive", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> << >>])
    >>
----


=============================================================================

---- CONFIG MCCosmosDB_TTrace ----
CONSTANTS
    Clients <- clients
    Regions <- regions
    WriteRegions <- regions
    Null = Null
    Data <- data
    Null = Null

PROPERTY
    \* _prop
    _implements

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

ALIAS
    _expression
=============================================================================
\* Generated on Wed Apr 13 14:59:26 PDT 2022