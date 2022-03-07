 $ tools/apalache/apalache/bin/apalache-mc check --cinit=ConstInit --inv=Session general-model/cosmos_client_apalache.tla

---------------------- MODULE cosmos_client_apalache -----------------------
(***************************************************************************)
(* Microsoft Azure Cosmos DB TLA+ specification for the five consistency   *)
(* levels the service offers. The spec focuses on the consistency          *)
(* guarantees Cosmos DB provides to the clients, without the details of    *)
(* the protocol implementation.                                            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache


\* @type: (Seq(Int), (a => Bool)) => Seq(Int);
FilterSeq(seq, cmp(_)) ==
    LET \* @type: (Seq(Int), Int) => Seq(Int);
        Frob(acc, e) == IF cmp(e) THEN acc \o <<e>> ELSE acc
    IN FoldSeq(Frob, <<>>, seq)

\* @type: (Seq(Int), Int) => Seq(Int);
SortedSeq(sorted, e) == 
    LET \* @type: Int => Bool;
        Gt(a) == a > e
        \* @type: Int => Bool;
        Lt(a) == a < e
    IN FilterSeq(sorted, Lt) \o <<e>> \o FilterSeq(sorted, Gt)

\* @type: (Seq(Int), Seq(Int)) => Seq(Int);
Merge(s1, s2) ==
    FoldSeq(SortedSeq, <<>>, s1 \o s2)

Last(s) ==
    s[Len(s)]

\* @type: Set(Int) => Int;
SetMax(S) ==
    IF S = {} THEN -1
    ELSE CHOOSE i \in S : \A j \in S : i >= j

\* @type: Seq(a) => Set(a);
SeqToSet(seq) ==
    {seq[i] : i \in DOMAIN seq}

(***************************************************************************)
(* Number of regions                                                       *)
(***************************************************************************)
CONSTANT 
    \* @type: Int;
    NumRegions
CONSTANT
    \* @type: Int;
    NumWriteRegions

ASSUME NumRegions \in Nat
ASSUME NumWriteRegions >= 1 /\ NumWriteRegions <= NumRegions

(***************************************************************************)
(* Number of clients per region for modeling                               *)
(***************************************************************************)
CONSTANT 
    \* @type: Int;
    NumClientsPerRegion

ASSUME NumClientsPerRegion \in Nat

(***************************************************************************)
(* MaxNumOp max number of operations from client                           *)
(***************************************************************************)
CONSTANT 
    \* @type: Int;
    MaxNumOp

(***************************************************************************)
(* Consistency level                                                       *)
(* (1) strong (Linearizability)                                            *)
(* (2) bounded (Bounded Staleness)                                         *)
(* (3) session                                                             *)
(* (4) prefix (Consistent Prefix)                                          *)
(* (5) eventual                                                            *)
(***************************************************************************)
CONSTANT 
    \* @type: Str;
    Consistency

ASSUME Consistency \in {"strong", "bounded_staleness", "session", "consistent_prefix", "eventual"}

(* The bounded version differences in Bounded Staleness consistency *)
CONSTANT 
    \* @type: Int;
    K

ASSUME K \in Nat

ConstInit ==
    /\ NumRegions = 2
    /\ NumWriteRegions = 2
    /\ NumClientsPerRegion = 2
    /\ MaxNumOp \in 1..5
    /\ Consistency = "session"
    /\ K = 1

(* All regions in topology *)
Regions ==
    \* @type: Set(Int); 
    1..NumRegions

(* All writable regions in topology *)
WriteRegions == 
    \* @type: Set(Int); 
    1..NumWriteRegions

(* All clients with local region *)
Clients ==
    \* @type: () => <<Int, Int>>);
    Regions \X (1..NumClientsPerRegion)
    \*{<<r, j>> : r \in Regions, j \in 1..NumClientsPerRegion}

(***************************************************************************)
(* All possible operations in history                                      *)
(***************************************************************************)
\* @typeAlias: OPERATION = [type: Str, data: Int, region: Int, client: <<Int, Int>>];
MCTypeAliases == TRUE

Operations ==
           [type: {"write"}, data: Nat, region: WriteRegions, client: Clients]
    \union [type: {"read"}, data: Nat, region: Regions, client: Clients]

VARIABLES 
    \* @type: Int;
    Bound,
    \* @type: Seq(OPERATION);
    History,
    \* @type: Int -> Int;
    Data,
    \* @type: Int -> Seq(Int);
    Database,
    \* @type: Int;
    value,
    \* @type: (<<Int, Int>> -> Str);
    pc

VARIABLES
    \* @type: (<<Int, Int>> -> Int);
    session_token,
    \* @type: (<<Int, Int>> -> Int);
    numOp

vars == << Bound, History, Data, Database, value, pc, session_token, numOp >>

ProcSet == (Clients) \cup {<<0, 0>>}

Init == (* Global variables *)
        /\ Bound = (CASE Consistency = "strong" -> 1
                      [] Consistency = "bounded_staleness" -> K
                      [] Consistency = "session" -> MaxNumOp
                      [] Consistency = "consistent_prefix" -> MaxNumOp
                      [] Consistency = "eventual" -> MaxNumOp)
        /\ History = <<>>
        /\ Data = [r \in Regions |-> 0]
        /\ Database = [r \in Regions |-> <<>>]
        /\ value = 0
        (* Process client *)
        /\ session_token = [self \in Clients |-> 0]
        /\ numOp = [self \in Clients |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "client_actions"
                                        [] self = <<0, 0>> -> "database_action"]

client_actions(self) == /\ pc[self] = "client_actions"
                        /\ IF numOp[self] < MaxNumOp
                              THEN /\ numOp' = [numOp EXCEPT ![self] = numOp[self] + 1]
                                   /\ \/ /\ pc' = [pc EXCEPT ![self] = "write"]
                                      \/ /\ pc' = [pc EXCEPT ![self] = "read"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ numOp' = numOp
                        /\ UNCHANGED << Bound, History, Data, Database, value, 
                                        session_token >>

write(self) == /\ pc[self] = "write"
               /\ value' = value + 1
               /\ IF self[1] \in WriteRegions
                     THEN /\ \A i, j \in Regions : Data[i] - Data[j] < Bound
                          /\ Database' = [Database EXCEPT ![self[1]] = Append(@, value')]
                          /\ Data' = [Data EXCEPT ![self[1]] = value']
                          /\ History' = Append(History, [type |-> "write",
                                                         data |-> value',
                                                       region |-> self[1],
                                                       client |-> self])
                          /\ session_token' = [session_token EXCEPT ![self] = value']
                     ELSE /\ TRUE
                          /\ UNCHANGED << History, Data, Database, 
                                          session_token >>
               /\ pc' = [pc EXCEPT ![self] = "client_actions"]
               /\ UNCHANGED << Bound, numOp >>

read(self) == /\ pc[self] = "read"
              /\ Consistency /= "session" \/ Data[self[1]] >= session_token[self]
              /\ Consistency /= "strong" \/ \A i, j \in Regions : Data[i] = Data[j]
              /\ History' = Append(History, [type |-> "read",
                                             data |-> Data[self[1]],
                                           region |-> self[1],
                                           client |-> self])
              /\ session_token' = [session_token EXCEPT ![self] = Data[self[1]]]
              /\ pc' = [pc EXCEPT ![self] = "client_actions"]
              /\ UNCHANGED << Bound, Data, Database, value, numOp >>

client(self) == client_actions(self) \/ write(self) \/ read(self)

database_action == /\ pc[<<0, 0>>] = "database_action"
                   /\ \E s \in WriteRegions:
                        \E d \in Regions:
                          /\ Database' = [Database EXCEPT ![d] = Merge(Database[d], Database[s])]
                          /\ IF Len(Database'[d]) > 0
                                THEN /\ Data' = [Data EXCEPT ![d] = Last(Database'[d])]
                                ELSE /\ TRUE
                                     /\ Data' = Data
                   /\ pc' = [pc EXCEPT ![<<0, 0>>] = "database_action"]
                   /\ UNCHANGED << Bound, History, value, session_token, numOp >>

CosmosDB == database_action

Next == CosmosDB
           \/ (\E self \in Clients: client(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(client(self))
        /\ WF_vars(CosmosDB)

-----------------------------------------------------------------------------


(* Operation in history h is monitonic *)
\* @type: (Int -> OPERATION) => Bool;
Monotonic(history) ==
    \A i, j \in DOMAIN history :
        i <= j => history[i]["data"] <= history[j]["data"]

(* Reads from client c are monotonic *)
MonotonicReadPerClient(c) == 
    LET reads == [i \in {j \in DOMAIN History :
                            /\ History[j].type = "read" 
                            /\ History[j].client = c} 
                 |-> History[i] ]
    IN Monotonic(reads)

(* Clients read their own writes *)
ReadYourWrite == \A i, j \in DOMAIN History : /\ i < j
                                              /\ History[i].type = "write"
                                              /\ History[j].type = "read"
                                              /\ History[i].client = History[j].client
                                              => History[j].data >= History[i].data

Session == 
    /\ \A c \in Clients : 
        MonotonicReadPerClient(c)
    /\ ReadYourWrite

====
(* Reads in region r are monotonic *)
MonotonicReadPerRegion(r) == LET reads == [i \in {j \in DOMAIN History : /\ History[j].type = "read" 
                                                                         /\ History[j].region = r}
                                          |-> History[i]]
                              IN Monotonic(reads)

(* Reads from client c are monotonic *)
MonotonicReadPerClient(c) == LET reads == [i \in {j \in DOMAIN History : /\ History[j].type = "read" 
                                                                         /\ History[j].client = c} 
                                          |-> History[i]]
                              IN Monotonic(reads)
                             
MonotonicWritePerRegion(r) == LET writes == [i \in {j \in DOMAIN History : /\ History[j].type = "write" 
                                                                           /\ History[j].region = r} 
                                            |-> History[i]]
                               IN Monotonic(writes)

(* Clients read their own writes *)
ReadYourWrite == \A i, j \in DOMAIN History : /\ i < j
                                              /\ History[i].type = "write"
                                              /\ History[j].type = "read"
                                              /\ History[i].client = History[j].client
                                              => History[j].data >= History[i].data
                                              
(* Read the latest writes *)
ReadAfterWrite == \A i, j \in DOMAIN History : /\ i < j
                                               /\ History[i].type = "write"
                                               /\ History[j].type = "read"
                                               => History[j].data >= History[i].data
                                               
Linearizability == \A i, j \in DOMAIN History : /\ i < j
                                                => History[j].data >= History[i].data
                                               
\* LastOperation(c) == LET i == SetMax({j \in DOMAIN History : History[j].client = c})
\*                     IN IF i > 0 THEN History[i] ELSE <<>>


\* BoundedStaleness == /\ \A i, j \in Regions : Data[i] - Data[j] <= K
\*                     /\ \A r \in Regions : MonotonicReadPerRegion(r)
\*                     /\ ReadYourWrite

\* ConsistentPrefix == \A r \in Regions : /\ MonotonicWritePerRegion(r)
\*                                        /\ AnyReadPerRegion(r)

Strong == /\ Linearizability
          /\ Monotonic(History)
          /\ ReadAfterWrite

Session == /\ \A c \in Clients : MonotonicReadPerClient(c)
           /\ ReadYourWrite

Eventual == \A i \in DOMAIN History : 
            LET r == History[i].region
            IN History[i].data \in {Database[r][j] : j \in DOMAIN Database[r]} \union {0}

\* Invariant == /\ TypeOK
\*              /\ CASE Consistency = "strong" -> Strong
\*                   [] Consistency = "bounded_staleness" -> BoundedStaleness
\*                   [] Consistency = "session" -> Session
\*                   [] Consistency = "consistent_prefix" -> ConsistentPrefix
\*                   [] Consistency = "eventual" -> Eventual

\* Liveness == <>[] (\A i, j \in Regions : Database[i] = Database[j])

=============================================================================
\* Authored by Cosmos DB
