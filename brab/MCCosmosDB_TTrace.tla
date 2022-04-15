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

VARIABLE _index

_prop ==
    ~<>[](
        /\ database = (_trace[_index][Len(_trace[_index])].database)
        /\ pc = (_trace[_index][Len(_trace[_index])].pc)
        /\ session = (_trace[_index][Len(_trace[_index])].session)
        /\ client = (_trace[_index][Len(_trace[_index])].client)
        /\ outbox = (_trace[_index][Len(_trace[_index])].outbox)
        /\ inbox = (_trace[_index][Len(_trace[_index])].inbox)
    )
----

_init ==
    /\ _index \in 1..Len(_trace)
    /\ database = _trace[_index][1].database
    /\ pc = _trace[_index][1].pc
    /\ outbox = _trace[_index][1].outbox
    /\ session = _trace[_index][1].session
    /\ client = _trace[_index][1].client
    /\ inbox = _trace[_index][1].inbox
----

_next ==
    /\ UNCHANGED _index
    /\ \E i,j \in DOMAIN _trace[_index]:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ database  = _trace[_index][i].database
        /\ database' = _trace[_index][j].database
        /\ pc  = _trace[_index][i].pc
        /\ pc' = _trace[_index][j].pc
        /\ outbox  = _trace[_index][i].outbox
        /\ outbox' = _trace[_index][j].outbox
        /\ session  = _trace[_index][i].session
        /\ session' = _trace[_index][j].session
        /\ client  = _trace[_index][i].client
        /\ client' = _trace[_index][j].client
        /\ inbox  = _trace[_index][i].inbox
        /\ inbox' = _trace[_index][j].inbox

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
        <<
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"read", "read">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> <<>>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"read", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 2] :> 1)]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"read", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> << >>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"receive", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1] :> 1)]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"receive", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> << >>])
        >>,
        <<
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"read", "read">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> <<>>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"read", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 2] :> 1)]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"read", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> << >>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"receive", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1] :> 1)]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"receive", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> << >>])
        >>
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