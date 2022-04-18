---- MODULE MCCosmosDB -----
EXTENDS CosmosDB

clients ==
    {1,2}
        
data ==
    Nat

regions ==
    {"R"}
        
MaxRequest ==
    \* /\ BagCardinality(inbox) < 5
    /\ Len(database) < 15

IsEven(n) ==
    n % 2 = 0

Level ==
    \* TRUE
    \* TLCGet("level") < 21
    /\ Len(database) < 10
    \* /\ ~IsEven(LastData)

Consistent ==
    \* This is not a theorem, because clients write non-monotonic data (values)
    \* into Cosmos.
    \* TODO: State this in terms of each doc's (partition) LSN.
    \A i,j \in 1..Len(database):
        (i < j /\ database[i].type = "Write" /\ database[j].type = "Write" )
        => (database[i].consistency.lsn) <= (database[j].consistency.lsn)
        \* => Len(database[i].data) <= Len(database[j].data)

    \* The MSFT internal Cosmos.tla spec by Eddie defines Linearizability as:
    \*
        \* Linearizability ==
        \* \A i, j \in Operations :
        \*     \* Only check operations whose response has been recorded and is no longer pending.
        \*     /\ LSN[i] # 0 /\ LSN[j] # 0
        \*     /\ times[j][2] # Pending 
        \*     => (times[i][1] >= times[j][2] => LSN[i] >= LSN[j])
    \* 
    \* IIf the start-timestamp of operation i is greater than or equal to the end-timestamp of
    \* operation j, the LSN of i is greater than or equal j's LSN.
    \* In this specification, we abstract from start- and end-timestamps, and, thus, have to
    \* define Linearizability in terms of LSNs.


NoErrorInPerpetuity ==
    <>[](\A c \in Clients: pc[c] # "error")

NoReceiveInPerpetuity ==
    <>[](\A c \in Clients: pc[c] # "receive")
    
Progress ==
    <>[](LastData("doc1") = 10)

Docs ==
    LET Writes == { w \in Range(database): w.type = "Write" }
    IN { w.doc : w \in Writes}

Alias ==
    [
        client |-> client,
        database |-> database,
        inbox |-> inbox,
        outbox |-> outbox,
        pc |-> pc,
        session |-> session,
        kv |-> [ d \in Docs |-> LastData(d) ]
    ]
======