------------------------------- MODULE Workflow --------------------------------
EXTENDS Integers, TLC, Sequences, SequencesExt, Bags, BagsExt

ARM ==
    "F"

Worker ==
    {"D", "R"}

\* Turn Clients into a CONSTANT
Clients ==
    Worker \cup {ARM}
    
--------------------------------------------------------------------------------

CONSTANT Data, Null

Levels ==
    {"Strong", "Bounded_staleness", "Session", "Consistent_prefix", "Eventual"}

STRNG ==
    [level |-> "Strong", token |-> -1 ]

SSSN(token) ==
    [level |-> "Session", token |-> token ]

Consistency ==
    [level: Levels, lsm: Int]

Cosmos ==
    "Cosmos"

\* Turn Regions into a CONSTANT
Regions ==
    {ARM} \cup Worker

WriteRegions ==
    Regions
    
--------------------------------------------------------------------------------

\* Request: Client -> Cosmos
Request ==
    [
        doc: STRING,     \* The document that was read.
        data: Data,    \* The data that was read.
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
        orig: {Cosmos}
    ] \cup 
    [
        doc: STRING,       \* The document that was written.
        data: {Null},      \* Null
        \* In case of error, the write might or might not have succeeded. An error
        \* models the case that the database response to a write request was lost.
        \* Message duplications is assumed to be prevented by the communicaion
        \* protocol (e.g. TCP).
        type: {"ACK", "NACK", "Error"},
        consistency: Consistency, 
        region: WriteRegions, \* The region the original read request was sent to.
        orig: {Cosmos}
    ]

VARIABLE
    outbox,
    \* A bag (multiset) of requests.
    inbox,
    \* A sequence of requests.
    database

TypeOK ==
    /\ outbox \in [ Clients -> Response ]
    /\ IsABag(inbox)
    /\ DOMAIN inbox \subseteq Request
    /\ database \in Seq(Request)

ReadResponse(request) ==
    {}

WriteResponse(request) ==
    \* Success or failure.
    {}

CosmosRead ==
    \* Non-deterministically read from the channel.
    \E req \in DOMAIN inbox:
        \/ \* Loose the request.
           /\ BagRemove(inbox, req)
           /\ UNCHANGED <<database, outbox>>
        \/ \* Handle the request.
           \/ /\ req.type = "Read"
              /\ database' = Append(database, req)
              /\ \/ \E res \in ReadResponse(req):
                        outbox' = [outbox EXCEPT ![req.origin] = Append(@, res)]
                 \/ UNCHANGED outbox \* Response is lost.
              /\ BagRemove(inbox, req)
           \/ /\ req.type = "Write"
              /\ database' = Append(database, req)
              /\ \/ \E res \in WriteResponse(req):
                        outbox' = [outbox EXCEPT ![req.origin] = Append(@, res)]
                 \/ UNCHANGED outbox \* Response is lost.
              /\ BagRemove(inbox, req)

Init ==
    /\ outbox = [ c \in Clients |-> <<>> ]
    /\ inbox = <<>>
    /\ database = <<>>

Next ==
    \/ LET req == []
       IN inbox' = BagAdd(inbox, req)
    \/ CosmosRead
    
======
--------------------------------------------------------------------------------

Writes(db, doc) ==
    FoldLeft(LAMBDA acc, e: IF e.type = "Write" /\ e.doc = doc THEN acc \o <<e>> ELSE acc,
             <<>>, db)

(* --fair algorithm Workflow {

    variables
        AzureQueue = <<>>;

        \* chan decouples cosmos from the client.
        chan = [n \in {ARM, Cosmos} \cup Worker |-> <<>>];  \* FIFO channels 

    macro send(des, msg) {
        chan[des] := Append(chan[des], msg);
    }

    macro receive(p, msg) {
        await Len(chan[p]) > 0;
        msg := Head(chan[p]);
        chan[p] := Tail(chan[p]);
    }

    \* Upon receipt of a (client) request, the database either replies with the expected response, 
    \* an error, or not at all.  The last case is futher divided into two cases s.t. the (write) 
    \* operation is performed but the response is lost or that the write does not happen.

    \* The database is modeled as a sequence of the read and write requests, from which the response
    \* has to be derived.  Even with multiple (read or write) regions, the database is still a
    \* single sequence.  Contrary to a real system, the database exposes its internal state to the
    \* client.  The client state, ie. the previous response, has to be part of the next request.

    \* We model the communication between clients and Cosmos via channels to decouple both sides at
    \* the TLA+ level.
    process (cosmos = Cosmos)
    variables
        Database = <<>>; msg;    
    {D: while(TRUE) {
           receive(Cosmos, msg);
           Database := Append(Database, msg);
        
           if (msg.type="Write"){
                                                     \* what should be the response to a write (the previous value, the new value, what does cosmos return)?
    DW:       send(msg.orig, [type|-> "Ack", data|->Database[Len(Database)], ses|->Len(Database)]);}             

    \*        else if (msg.consistency="Eventual")
    \* DP:       with (k \in 1..Len(Database))
    \*              send(msg.orig, [type|-> "Reply", data|->Database[k], ses|->-1]);
        
    \*        else if (msg.consistency="Session")
    \* DS:       with (k \in msg.ses..Len(Database))
    \*              send(msg.orig, [type|-> "Reply", dat|->Database[k], ses|->k]);

           else if (msg.consistency=STRNG)                  
    DG:       with (k= Len(Writes(Database, msg.doc)))
                 send(msg.orig, [type|-> "Reply", data|->Writes(Database, msg.doc)[k].data, ses|->-1]);          
       }
    }

    \* Frontdoor ARM
    process (a = ARM)
        variables amsg;
    {
     arml:  send(Cosmos, Write(STRNG, "F", "r1", "rg", ARM));
     armi:  receive(ARM, amsg); \* Ack
            AzureQueue := Append(AzureQueue, [ job |-> "vm" ]); \* ARM enqueues jobs into Azure Strogae Queue.
    }

    \* Worker
    process (worker \in Worker)
        variable wmsg;
    {
            \* Steal the job by dequeueing from an Azure storge queue: (https://docs.microsoft.com/en-us/azure/storage/queues/storage-queues-introduction)
     wrko:  when AzureQueue # <<>>;
            wmsg := Head(AzureQueue);
            AzureQueue := Tail(AzureQueue);
           
     wrkf:  send(Cosmos, Read(STRNG, self, "rg", self));
     wrke:  receive(self, wmsg); \* Ack
            assert wmsg.data # "";

     wrkd:  send(Cosmos, Write(STRNG, self, wmsg.data, "vm", self));
     wrkw:  receive(self, wmsg); \* Ack
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "cd7e92ed")
CONSTANT defaultInitValue
VARIABLES AzureQueue, chan, pc, Database, msg, amsg, wmsg

vars == << AzureQueue, chan, pc, Database, msg, amsg, wmsg >>

ProcSet == {Cosmos} \cup {ARM} \cup (Worker)

Init == (* Global variables *)
        /\ AzureQueue = <<>>
        /\ chan = [n \in {ARM, Cosmos} \cup Worker |-> <<>>]
        (* Process cosmos *)
        /\ Database = <<>>
        /\ msg = defaultInitValue
        (* Process a *)
        /\ amsg = defaultInitValue
        (* Process worker *)
        /\ wmsg = [self \in Worker |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = Cosmos -> "D"
                                        [] self = ARM -> "arml"
                                        [] self \in Worker -> "wrko"]

D == /\ pc[Cosmos] = "D"
     /\ Len(chan[Cosmos]) > 0
     /\ msg' = Head(chan[Cosmos])
     /\ chan' = [chan EXCEPT ![Cosmos] = Tail(chan[Cosmos])]
     /\ Database' = Append(Database, msg')
     /\ IF msg'.type="Write"
           THEN /\ pc' = [pc EXCEPT ![Cosmos] = "DW"]
           ELSE /\ IF msg'.consistency=STRNG
                      THEN /\ pc' = [pc EXCEPT ![Cosmos] = "DG"]
                      ELSE /\ pc' = [pc EXCEPT ![Cosmos] = "D"]
     /\ UNCHANGED << AzureQueue, amsg, wmsg >>

DW == /\ pc[Cosmos] = "DW"
      /\ chan' = [chan EXCEPT ![(msg.orig)] = Append(chan[(msg.orig)], ([type|-> "Ack", data|->Database[Len(Database)], ses|->Len(Database)]))]
      /\ pc' = [pc EXCEPT ![Cosmos] = "D"]
      /\ UNCHANGED << AzureQueue, Database, msg, amsg, wmsg >>

DG == /\ pc[Cosmos] = "DG"
      /\ LET k == Len(Writes(Database, msg.doc)) IN
           chan' = [chan EXCEPT ![(msg.orig)] = Append(chan[(msg.orig)], ([type|-> "Reply", data|->Writes(Database, msg.doc)[k].data, ses|->-1]))]
      /\ pc' = [pc EXCEPT ![Cosmos] = "D"]
      /\ UNCHANGED << AzureQueue, Database, msg, amsg, wmsg >>

cosmos == D \/ DW \/ DG

arml == /\ pc[ARM] = "arml"
        /\ chan' = [chan EXCEPT ![Cosmos] = Append(chan[Cosmos], (Write(STRNG, "F", "r1", "rg", ARM)))]
        /\ pc' = [pc EXCEPT ![ARM] = "armi"]
        /\ UNCHANGED << AzureQueue, Database, msg, amsg, wmsg >>

armi == /\ pc[ARM] = "armi"
        /\ Len(chan[ARM]) > 0
        /\ amsg' = Head(chan[ARM])
        /\ chan' = [chan EXCEPT ![ARM] = Tail(chan[ARM])]
        /\ AzureQueue' = Append(AzureQueue, [ job |-> "vm" ])
        /\ pc' = [pc EXCEPT ![ARM] = "Done"]
        /\ UNCHANGED << Database, msg, wmsg >>

a == arml \/ armi

wrko(self) == /\ pc[self] = "wrko"
              /\ AzureQueue # <<>>
              /\ wmsg' = [wmsg EXCEPT ![self] = Head(AzureQueue)]
              /\ AzureQueue' = Tail(AzureQueue)
              /\ pc' = [pc EXCEPT ![self] = "wrkf"]
              /\ UNCHANGED << chan, Database, msg, amsg >>

wrkf(self) == /\ pc[self] = "wrkf"
              /\ chan' = [chan EXCEPT ![Cosmos] = Append(chan[Cosmos], (Read(STRNG, self, "rg", self)))]
              /\ pc' = [pc EXCEPT ![self] = "wrke"]
              /\ UNCHANGED << AzureQueue, Database, msg, amsg, wmsg >>

wrke(self) == /\ pc[self] = "wrke"
              /\ Len(chan[self]) > 0
              /\ wmsg' = [wmsg EXCEPT ![self] = Head(chan[self])]
              /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
              /\ Assert(wmsg'[self].data # "", 
                        "Failure of assertion at line 216, column 13.")
              /\ pc' = [pc EXCEPT ![self] = "wrkd"]
              /\ UNCHANGED << AzureQueue, Database, msg, amsg >>

wrkd(self) == /\ pc[self] = "wrkd"
              /\ chan' = [chan EXCEPT ![Cosmos] = Append(chan[Cosmos], (Write(STRNG, self, wmsg[self].data, "vm", self)))]
              /\ pc' = [pc EXCEPT ![self] = "wrkw"]
              /\ UNCHANGED << AzureQueue, Database, msg, amsg, wmsg >>

wrkw(self) == /\ pc[self] = "wrkw"
              /\ Len(chan[self]) > 0
              /\ wmsg' = [wmsg EXCEPT ![self] = Head(chan[self])]
              /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << AzureQueue, Database, msg, amsg >>

worker(self) == wrko(self) \/ wrkf(self) \/ wrke(self) \/ wrkd(self)
                   \/ wrkw(self)

Next == cosmos \/ a
           \/ (\E self \in Worker: worker(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 

Success ==
    \* One worker will successfully create the VM.
    /\ LET f == FoldLeft(LAMBDA acc, e:
                                IF e.doc = "vm" /\ e.data = "r1" THEN acc \o <<e>> ELSE acc,
                                <<>>, Database)
       IN <>[](Len(f) = 1)
    /\ <>[](\A p \in DOMAIN chan: chan[p] = <<>>)
    /\ <>[](AzureQueue = <<>>)

================================================================================


\* CONSTANT 
\* Values ==
\*     \* [ i \in 0..19 |-> i ]
\*     \* <<0,13,4,2,19,7,10,8,15,17,1,3,9,18,6,12,11,5,14>>
\*     \* <<5,25,14,33,17,11,18,16,6,30,2,10,13,28,29,34,22,36,32,12,23,4,20,26,19,21,31,7,35,27,24,9,8,3,15,1>>
\*     LET LCG(x) == ((5 * x) + 0) % 37 \* https://en.wikipedia.org/wiki/Lehmer_random_number_generator
\*         sum[ n \in 1..36 ] == IF n = 1 THEN LCG(n) ELSE LCG(sum[n-1])
\*     IN sum

\* VARIABLE ops
\* vars == <<history, ops>>

\* Init ==
\*     /\ DB!Init
\*     /\ ops = 1
