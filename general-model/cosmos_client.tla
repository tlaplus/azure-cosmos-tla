--------------------------- MODULE cosmos_client ----------------------------
(***************************************************************************)
(* Microsoft Azure Cosmos DB TLA+ specification for the five consistency   *)
(* levels the service offers. The spec focuses on the consistency          *)
(* guarantees Cosmos DB provides to the clients, without the details of    *)
(* the protocol implementation.                                            *)
(***************************************************************************)

EXTENDS Naturals, Integers, Reals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Number of regions                                                       *)
(***************************************************************************)
CONSTANT NumRegions
CONSTANT NumWriteRegions

ASSUME NumRegions \in Nat
ASSUME NumWriteRegions >= 1 /\ NumWriteRegions <= NumRegions

(***************************************************************************)
(* Number of clients per region for modeling                               *)
(***************************************************************************)
CONSTANT NumClientsPerRegion

ASSUME NumClientsPerRegion \in Nat

(***************************************************************************)
(* MaxNumOp max number of operations from client                           *)
(***************************************************************************)
CONSTANT MaxNumOp

(***************************************************************************)
(* Consistency level                                                       *)
(* (1) strong (Linearizability)                                            *)
(* (2) bounded (Bounded Staleness)                                         *)
(* (3) session                                                             *)
(* (4) prefix (Consistent Prefix)                                          *)
(* (5) eventual                                                            *)
(***************************************************************************)
CONSTANT Consistency

ASSUME Consistency \in {"strong", "bounded_staleness", "session", "consistent_prefix", "eventual"}

(* The bounded version differences in Bounded Staleness consistency *)
CONSTANT K

ASSUME K \in Nat

Range(f) ==
    {f[x]: x \in DOMAIN f}

Values ==
    \* [ i \in 0..19 |-> i ]
    \* <<0,13,4,2,19,7,10,8,15,17,1,3,9,18,6,12,11,5,14>>
    \* <<5,25,14,33,17, 11, 18, 16, 6, 30, 2, 10, 13, 28, 29, 34, 22, 36, 32, 12, 23, 4, 20, 26, 19, 21, 31, 7, 35, 27, 24, 9, 8, 3, 15, 1>>
    LET LCG(x) == ((5 * x) + 0) % 37 \* https://en.wikipedia.org/wiki/Lehmer_random_number_generator
        sum[ n \in 1..36 ] == IF n = 1 THEN LCG(n) ELSE LCG(sum[n-1])
    IN sum

NextValue(oldValue) ==
    \* HACK!!!
    LET idx == CHOOSE i \in DOMAIN Values: Values[i] = oldValue
    IN Values[idx + 1]

Suffix(value) ==
    \* Inclusive
    LET idx == CHOOSE i \in DOMAIN Values: Values[i] = value
    IN { Values[i] : i \in idx..Len(Values) }

Prefix(value) ==
    \* Inclusive
    LET idx == CHOOSE i \in DOMAIN Values: Values[i] = value
    IN { Values[i] : i \in 1..idx }

PrefixOf(values) ==
    \* Inclusive
    LET idx == CHOOSE idx \in 0..Len(Values) : { Values[i] : i \in 1..idx } = values
    IN SubSeq(Values, 1, idx)

\* ASSUME PrintT(Values)

(* All regions in topology *)
Regions == 1..NumRegions
(* All writable regions in topology *)
WriteRegions == 1..NumWriteRegions
(* All clients with local region *)
Clients == {<<r, j>> : r \in Regions, j \in 1..NumClientsPerRegion}

(***************************************************************************)
(* All possible operations in history                                      *)
(***************************************************************************)
Operations == [type: {"write"}, data: Nat, region: WriteRegions, client: Clients]
       \union [type: {"read"}, data: Nat, region: Regions, client: Clients]

(* --algorithm cosmos_client
{

    variables (* Max staleness. Strong is a special case of bounded with K = 1 *)
              Bound = CASE Consistency = "strong" -> 1
                        [] Consistency = "bounded_staleness" -> K
                        [] Consistency = "session" -> MaxNumOp
                        [] Consistency = "consistent_prefix" -> MaxNumOp
                        [] Consistency = "eventual" -> MaxNumOp;
                        
              (* Client operation history *)
              History = <<>>;
              
              (* Latest data value in each region *)
              Data = [r \in Regions |-> Head(Values)];
              
              (* Tentative log in each region *)
              Database = [r \in Regions |-> <<Head(Values)>>];
              
              (* Value used by clients *)
              value = Head(Values);
              
    define {
        \* Removing duplicates from a sequence:
        RECURSIVE RemDupRec(_,_)
        RemDupRec(es, seen) == IF es = <<>> THEN <<>>
                               ELSE IF es[1] \in seen THEN RemDupRec(Tail(es), seen)
                               ELSE <<es[1]>> \o RemDupRec(Tail(es), seen \cup {es[1]})
                                         
        RemoveDuplicates(es) == RemDupRec(es, {})
        
        SetMax(S) == IF S = {} THEN -1
                     ELSE CHOOSE i \in S : \A j \in S : i >= j \* FiniteSetsExt!Max
                     
        SeqToSet(s) == {s[i] : i \in DOMAIN s} \* Functions!Range
                     
        Last(s) == s[Len(s)] \* SequencesExt!Last
    }
    
    (* -------------------------------------------------------------- *)
    (* --------------------- CLIENT ACTIONS ------------------------- *)
    (* -------------------------------------------------------------- *)
    
    (* Regular write at local region *)
    macro write(v)
    {
        if (self[1] \in WriteRegions)
        {
            when \A i, j \in Regions : Data[i] - Data[j] < Bound;
            Database[self[1]] := Append(@, v);
            Data[self[1]] := v;
            History := Append(History, [type |-> "write",
                                        data |-> v,
                                      region |-> self[1],
                                      client |-> self]);
            session_token := v;
        }
    }
    
    (* Reads with consistency checks *)
    macro read()
    {
        (* We check session token for session consistency *)
        when Consistency /= "session" \/ Data[self[1]] >= session_token;
        (* We check global value for strong consistency *)
        when Consistency /= "strong" \/ \A i, j \in Regions : Data[i] = Data[j];
        History := Append(History, [type |-> "read",
                                    data |-> Data[self[1]],
                                  region |-> self[1],
                                  client |-> self]);
        session_token := Data[self[1]];
    }
    
    (* -------------------------------------------------------------- *)
    (* --------------------- REGION ACTIONS ------------------------- *)
    (* -------------------------------------------------------------- *)
    
    (* Asynchronously replicates from source region to destination region and merges data history *)
    macro replicate()
    {
        with (s \in WriteRegions; d \in Regions)
        {
            \* Database[d] := RemoveDuplicates((Database[d] \o Database[s]));
            Database[d] := PrefixOf(Range(Database[d]) \cup Range(Database[s]));
            if (Len(Database[d]) > 0)
            {
                Data[d] := Last(Database[d]);
            }
        }
    }
    
    (* -------------------------------------------------------------- *)
    (* -------------------- CLIENT PROCESSES ------------------------ *)
    (* -------------------------------------------------------------- *)
    fair process (client \in Clients)
    variable session_token = 1;
    numOp = 0;
    {
        client_actions:
        while(numOp < MaxNumOp)
        {
            numOp := numOp + 1;
            either
            {
                write:
                value := NextValue(value);
                write(value);
            }
            or read: read();
        }
    }
    
    (* -------------------------------------------------------------- *)
    (* -------------------- SERVER PROCESSES ------------------------ *)
    (* -------------------------------------------------------------- *)
    fair process (CosmosDB = <<0, 0>>)
    {
        database_action:
        while(TRUE)
        {
            replicate();
        }
    }
    
}
*)
\* BEGIN TRANSLATION
VARIABLES Bound, History, Data, Database, value, pc

(* define statement *)
RECURSIVE RemDupRec(_,_)
RemDupRec(es, seen) == IF es = <<>> THEN <<>>
                       ELSE IF es[1] \in seen THEN RemDupRec(Tail(es), seen)
                       ELSE <<es[1]>> \o RemDupRec(Tail(es), seen \cup {es[1]})

RemoveDuplicates(es) == RemDupRec(es, {})

SetMax(S) == IF S = {} THEN -1
             ELSE CHOOSE i \in S : \A j \in S : i >= j

SeqToSet(s) == {s[i] : i \in DOMAIN s}

Last(s) == s[Len(s)]

VARIABLES session_token, numOp

vars == << Bound, History, Data, Database, value, pc, session_token, numOp >>

ProcSet == (Clients) \cup {<<0, 0>>}

Init == (* Global variables *)
        /\ Bound = (CASE Consistency = "strong" -> 1
                      [] Consistency = "bounded_staleness" -> K
                      [] Consistency = "session" -> MaxNumOp
                      [] Consistency = "consistent_prefix" -> MaxNumOp
                      [] Consistency = "eventual" -> MaxNumOp)
        /\ History = <<>>
        /\ Data = [r \in Regions |-> Head(Values)]
        /\ Database = [r \in Regions |-> <<Head(Values)>>]
        /\ value = Head(Values)
        (* Process client *)
        /\ session_token = [self \in Clients |-> 1]
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
               /\ value' = NextValue(value)
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
                          /\ Database' = [Database EXCEPT ![d] = PrefixOf(Range(Database[d]) \cup Range(Database[s]))]
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

\* END TRANSLATION


-----------------------------------------------------------------------------

(* enable these invariants in model checker *)

(* Check elements in History are type of Opertion *)
TypeOK == {History[i] : i \in DOMAIN History} \subseteq Operations

(* Read value in any regional database history *)                       
AnyReadPerRegion(r) == \A i \in DOMAIN History : /\ History[i].type = "read"
                                                 /\ History[i].region = r
                                                 => History[i].data \in SeqToSet(Database[r]) \union {0}

(* Operation in history h is monitonic *)
Monotonic(h) == 
    \A i, j \in DOMAIN h : 
        i <= j => h[j].data \in Suffix(h[i].data)

(* Reads in region r are monotonic *)
MonotonicReadPerRegion(r) == LET reads == [i \in {j \in DOMAIN History : /\ History[j].type = "read" 
                                                                         /\ History[j].region = r}
                                          |-> History[i]]
                              IN Monotonic(reads)

(* Reads from client c are monotonic *)
MonotonicReadPerClient(c) ==
    LET reads == 
            [   
                i \in 
                    {j \in DOMAIN History : /\ History[j].type = "read" 
                                            /\ History[j].client = c} 
                |-> History[i]
            ]
    IN Monotonic(reads)
                             
MonotonicWritePerRegion(r) == LET writes == [i \in {j \in DOMAIN History : /\ History[j].type = "write" 
                                                                           /\ History[j].region = r} 
                                            |-> History[i]]
                               IN Monotonic(writes)

(* Clients read their own writes *)
ReadYourWrite == 
    \A i, j \in DOMAIN History : 
        /\ i < j
        /\ History[i].type = "write"
        /\ History[j].type = "read"
        /\ History[i].client = History[j].client
        => History[j].data \in Suffix(History[i].data)
                                              
(* Read the latest writes *)
ReadAfterWrite ==
    \A i, j \in DOMAIN History :
        /\ i < j
        /\ History[i].type = "write"
        /\ History[j].type = "read"
        => History[j].data \in Suffix(History[i].data)
                                               
Linearizability ==
    \A i, j \in DOMAIN History :
        i < j => History[i].data \in Prefix(History[j].data)
                                               
LastOperation(c) == LET i == SetMax({j \in DOMAIN History : History[j].client = c})
                    IN IF i > 0 THEN History[i] ELSE <<>>


BoundedStaleness == /\ \A i, j \in Regions : Data[i] - Data[j] <= K
                    /\ \A r \in Regions : MonotonicReadPerRegion(r)
                    /\ ReadYourWrite

ConsistentPrefix == \A r \in Regions : /\ MonotonicWritePerRegion(r)
                                       /\ AnyReadPerRegion(r)

Strong == /\ LIN:: Linearizability
          /\ MON:: Monotonic(History)
          /\ RAW:: ReadAfterWrite

Session == /\ MRPC:: \A c \in Clients : MonotonicReadPerClient(c)
           /\ RYW:: ReadYourWrite

Eventual == \A i \in DOMAIN History : 
            LET r == History[i].region
            IN History[i].data \in {Database[r][j] : j \in DOMAIN Database[r]} \union {0}

Invariant == /\ TypeOK
             /\ CASE Consistency = "strong" -> Strong
                  [] Consistency = "bounded_staleness" -> BoundedStaleness
                  [] Consistency = "session" -> Session
                  [] Consistency = "consistent_prefix" -> ConsistentPrefix
                  [] Consistency = "eventual" -> Eventual

Liveness == <>[] (\A i, j \in Regions : Database[i] = Database[j])

Diameter ==
    TLCGet("level") < 12

Alias ==
    [
        Data |-> Data,
        Database |-> Database,
        History |-> History,
        ses |-> session_token,
        SessionMRPC |-> Session!MRPC,
        SessionRYW |-> Session!RYW,
        StrongLIN |-> Strong!LIN,
        StrongMON |-> Strong!MON,
        StrongRAW |-> Strong!RAW
    ]
=============================================================================
\* Authored by Cosmos DB
