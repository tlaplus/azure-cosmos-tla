------------------------------- MODULE Workflow --------------------------------
EXTENDS Integers, TLC, Sequences, SequencesExt

Regions ==
    {"F", "D", "R"}

WriteRegions ==
    {"F", "D", "R"}

(* --fair algorithm Workflow {

    variables
        history = <<>>;

    define {
        DB == INSTANCE CosmosDB WITH Consistency <- "Strong"

        Success ==
            \* One worker will successfully create the VM.
            LET f == FoldLeft(LAMBDA acc, e:
                                IF e.doc = "vm" /\ e.data = "r1" THEN acc \o <<e>> ELSE acc,
                                <<>>, history)
            IN <>[](Len(f) = 1)
    }

    \* Frontdoor ARM
    process (a = "arm")
    {
        \* ARM writes job into database
        arm1: history := DB!Write(history, [region |-> "F", data |-> "j1", doc |-> "job"]);

        \* ARM writes Resource Group into database
        arm2: history := DB!Write(history, [region |-> "F", data |-> "r1", doc |-> "rg"]);
    }

    \* Worker
    process (worker \in {"D", "R"})
    {
        \* Steal the job by (atomically) "updating" the job in the database.
        wrk1: when "j1" \in DB!Read(history, [region |-> "F", doc |-> "job"]);
              history := DB!Write(history, [region |-> "F", data |-> self, doc |-> "job"]);
        
        \* Get the resource group from the database.
        wrk2: with (w \in DB!Read(history, [region |-> self, doc |-> "rg"])) {
                \* assert w # "";
                \* Create a resource such as a VM.
                history := DB!Write(history, [region |-> self, data |-> w, doc |-> "vm"]);
              }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "ada08041")
VARIABLES history, pc

(* define statement *)
DB == INSTANCE CosmosDB WITH Consistency <- "Strong"

Success ==

    LET f == FoldLeft(LAMBDA acc, e:
                        IF e.doc = "vm" /\ e.data = "r1" THEN acc \o <<e>> ELSE acc,
                        <<>>, history)
    IN <>[](Len(f) = 1)


vars == << history, pc >>

ProcSet == {"arm"} \cup ({"D", "R"})

Init == (* Global variables *)
        /\ history = <<>>
        /\ pc = [self \in ProcSet |-> CASE self = "arm" -> "arm1"
                                        [] self \in {"D", "R"} -> "wrk1"]

arm1 == /\ pc["arm"] = "arm1"
        /\ history' = DB!Write(history, [region |-> "F", data |-> "j1", doc |-> "job"])
        /\ pc' = [pc EXCEPT !["arm"] = "arm2"]

arm2 == /\ pc["arm"] = "arm2"
        /\ history' = DB!Write(history, [region |-> "F", data |-> "r1", doc |-> "rg"])
        /\ pc' = [pc EXCEPT !["arm"] = "Done"]

a == arm1 \/ arm2

wrk1(self) == /\ pc[self] = "wrk1"
              /\ "j1" \in DB!Read(history, [region |-> "F", doc |-> "job"])
              /\ history' = DB!Write(history, [region |-> "F", data |-> self, doc |-> "job"])
              /\ pc' = [pc EXCEPT ![self] = "wrk2"]

wrk2(self) == /\ pc[self] = "wrk2"
              /\ \E w \in DB!Read(history, [region |-> self, doc |-> "rg"]):
                   history' = DB!Write(history, [region |-> self, data |-> w, doc |-> "vm"])
              /\ pc' = [pc EXCEPT ![self] = "Done"]

worker(self) == wrk1(self) \/ wrk2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == a
           \/ (\E self \in {"D", "R"}: worker(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Alias ==
    [
        pc |-> pc,
        history |-> history,
        f |-> FoldLeft(LAMBDA acc, e: IF e.doc = "vm" THEN acc \o <<e>> ELSE acc, <<>>, history)
    ]
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
