---- MODULE MCCosmosDB_TTrace ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, MCCosmosDB, SequencesExt

VARIABLE _index

_trace ==
    LET MCCosmosDB_trace == INSTANCE MCCosmosDB_trace
    IN MCCosmosDB_trace!trace
----

RECURSIVE LatestRead(_,_,_)
LatestRead(t, j, c) ==
    IF j = 0
    THEN ""
    ELSE IF \E m \in Range(t[j].outbox[c]): m.type = "Reply"
         THEN (CHOOSE m \in Range(t[j].outbox[c]): m.type = "Reply").data
         ELSE LatestRead(t, j - 1, c)

_expression ==
    [
        \* database |-> database
        lastValue |-> LastData("doc1"),
        \* ,pc |-> pc
        \* ,outbox |-> outbox
        \* ,session |-> session
        \* ,
        client |-> client
        \* ,inbox |-> inbox
        ,_read |-> [ c \in Clients |-> 
            LatestRead(_trace[_index], TLCGet("level"), c) ]
    ]

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

_view ==
    <<vars, _index, TLCGet("level")>>

HL == INSTANCE MCCosmosDB
_implements == 
    HL!Init /\ [][HL!Next]_HL!vars

=============================================================================

---- MODULE MCCosmosDB_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, MCCosmosDB

=============================================================================

---- MODULE MCCosmosDB_trace ----
EXTENDS TLC, MCCosmosDB

trace == 
    <<
        <<
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"read", "read">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> <<>>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"receive", "read">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1] :> 1)]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1]>>,pc |-> <<"receive", "read">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<[data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>, <<>>>>,inbox |-> << >>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1]>>,pc |-> <<"receive", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<[data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 2] :> 1)]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1]>>,pc |-> <<"write", "receive">>,session |-> 1,client |-> <<[data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"], Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 2] :> 1)]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1]>>,pc |-> <<"write", "receive">>,session |-> 1,client |-> <<[data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"], Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 2] :> 1)]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1]>>,pc |-> <<"receive", "receive">>,session |-> 1,client |-> <<[data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"], Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 2] :> 1 @@ [data |-> 2, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 1] :> 1)]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1], [data |-> 2, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 1]>>,pc |-> <<"receive", "receive">>,session |-> 1,client |-> <<[data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"], Null>>,outbox |-> <<<<[data |-> 2, type |-> "ACK", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 2] :> 1)]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1], [data |-> 2, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 2]>>,pc |-> <<"receive", "receive">>,session |-> 1,client |-> <<[data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"], Null>>,outbox |-> <<<<[data |-> 2, type |-> "ACK", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>, <<[data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>>>,inbox |-> << >>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1], [data |-> 2, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 2]>>,pc |-> <<"receive", "write">>,session |-> 1,client |-> <<[data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"], [data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>,outbox |-> <<<<[data |-> 2, type |-> "ACK", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>, <<>>>>,inbox |-> << >>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1], [data |-> 2, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 2]>>,pc |-> <<"read", "write">>,session |-> 3,client |-> <<[data |-> 2, type |-> "ACK", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> "cosmos"], [data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>,outbox |-> <<<<>>, <<>>>>,inbox |-> << >>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1], [data |-> 2, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 2]>>,pc |-> <<"receive", "write">>,session |-> 3,client |-> <<[data |-> 2, type |-> "ACK", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> "cosmos"], [data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> 1] :> 1)])
        >>,
        <<
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 1]>>,pc |-> <<"read", "read">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> <<>>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 1]>>,pc |-> <<"receive", "read">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1] :> 1)]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1]>>,pc |-> <<"receive", "read">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<[data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>, <<>>>>,inbox |-> << >>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1]>>,pc |-> <<"write", "read">>,session |-> 1,client |-> <<[data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"], Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> << >>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1]>>,pc |-> <<"receive", "read">>,session |-> 1,client |-> <<[data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"], Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([data |-> 2, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 1] :> 1)]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1], [data |-> 2, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 1]>>,pc |-> <<"receive", "read">>,session |-> 1,client |-> <<[data |-> 1, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"], Null>>,outbox |-> <<<<[data |-> 2, type |-> "ACK", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>, <<>>>>,inbox |-> << >>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1], [data |-> 2, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 1]>>,pc |-> <<"read", "read">>,session |-> 3,client |-> <<[data |-> 2, type |-> "ACK", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> "cosmos"], Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> << >>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1], [data |-> 2, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 1]>>,pc |-> <<"read", "receive">>,session |-> 3,client |-> <<[data |-> 2, type |-> "ACK", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> "cosmos"], Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> 2] :> 1)]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1], [data |-> 2, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> 2]>>,pc |-> <<"read", "receive">>,session |-> 3,client |-> <<[data |-> 2, type |-> "ACK", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> "cosmos"], Null>>,outbox |-> <<<<>>, <<[data |-> 2, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>>>,inbox |-> << >>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1], [data |-> 2, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> 2]>>,pc |-> <<"read", "write">>,session |-> 3,client |-> <<[data |-> 2, type |-> "ACK", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> "cosmos"], [data |-> 2, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>,outbox |-> <<<<>>, <<>>>>,inbox |-> << >>]),
        ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1], [data |-> 2, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 1], [type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> 2]>>,pc |-> <<"read", "receive">>,session |-> 3,client |-> <<[data |-> 2, type |-> "ACK", doc |-> "doc1", consistency |-> [lsn |-> 3, level |-> "Session"], region |-> "R", orig |-> "cosmos"], [data |-> 2, type |-> "Reply", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> "cosmos"]>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([data |-> 4, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], old |-> Null, region |-> "R", orig |-> 2] :> 1)])
        >>
        \* ,<<
        \* ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"read", "read">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> <<>>]),
        \* ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"read", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 2] :> 1)]),
        \* ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"read", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> << >>]),
        \* ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"receive", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> ([type |-> "Read", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Session"], region |-> "R", orig |-> 1] :> 1)]),
        \* ([database |-> <<[data |-> 1, type |-> "Write", doc |-> "doc1", consistency |-> [lsn |-> 1, level |-> "Strong"], old |-> Null, region |-> "R", orig |-> 2]>>,pc |-> <<"receive", "receive">>,session |-> 1,client |-> <<Null, Null>>,outbox |-> <<<<>>, <<>>>>,inbox |-> << >>])
        \* >>
    >>

=============================================================================
