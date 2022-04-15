---- MODULE MCCosmosDB_TTrace ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, MCCosmosDB

_expression ==
    LET MCCosmosDB_TEExpression == INSTANCE MCCosmosDB_TEExpression
    IN MCCosmosDB_TEExpression!expression
----

_trace ==
    LET MCCosmosDB_TETrace == INSTANCE MCCosmosDB_TETrace
    IN MCCosmosDB_TETrace!trace
----

_prop ==
    ~<>[](
        /\ database = (_TETrace[Len(_TETrace)].database)
        /\ pc = (_TETrace[Len(_TETrace)].pc)
        /\ session = (_TETrace[Len(_TETrace)].session)
        /\ client = (_TETrace[Len(_TETrace)].client)
        /\ outbox = (_TETrace[Len(_TETrace)].outbox)
        /\ inbox = (_TETrace[Len(_TETrace)].inbox)
    )
----

_init ==
    /\ database = _TETrace[1].database
    /\ pc = _TETrace[1].pc
    /\ outbox = _TETrace[1].outbox
    /\ session = _TETrace[1].session
    /\ client = _TETrace[1].client
    /\ inbox = _TETrace[1].inbox
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ database  = _TETrace[i].database
        /\ database' = _TETrace[j].database
        /\ pc  = _TETrace[i].pc
        /\ pc' = _TETrace[j].pc
        /\ outbox  = _TETrace[i].outbox
        /\ outbox' = _TETrace[j].outbox
        /\ session  = _TETrace[i].session
        /\ session' = _TETrace[j].session
        /\ client  = _TETrace[i].client
        /\ client' = _TETrace[j].client
        /\ inbox  = _TETrace[i].inbox
        /\ inbox' = _TETrace[j].inbox

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

---- MODULE MCCosmosDB_TETrace ----
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

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Wed Apr 13 14:59:26 PDT 2022