------------------------------- MODULE CosmosDB -------------------------------
EXTENDS Naturals, Sequences, SequencesExt

LOCAL Filter(db, cmp(_)) ==
    FoldLeft(LAMBDA acc, e: IF cmp(e) THEN acc \o <<e>> ELSE acc,
             <<>>, db)

--------------------------------------------------------------------------------

CONSTANT 
    Consistency

ASSUME
    Consistency \in 
        {
            "Eventual",
            "Consistent_Prefix",
            "Session",
            "Bounded_Staleness",
            "Strong"
        }

CONSTANT
    Regions

CONSTANT
    WriteRegions

ASSUME
    WriteRegions \subseteq Regions

--------------------------------------------------------------------------------

\* Linearizability
ReadStrong(db, operation, var(_,_)) ==
    LET f == Filter(db, LAMBDA e: e.doc = operation.doc)
    IN IF f = <<>> THEN UNCHANGED var(FALSE, 1)
       ELSE var(TRUE, Last(f).data)

\* consistent-prefix
\* monotonic reads
\* monotonic writes
\* read-your-writes
\* write-follows-reads guarantees
ReadSession(db, token, operation, var(_,_)) ==
    TRUE
    \* LET f == Filter(SubSeq(db, token, Len(db)), LAMBDA e: e.doc = operation.doc)
    \* IN IF f = <<>> THEN UNCHANGED var
    \*    ELSE \E v \in {f[i].data : i \in 1..Len(f)} : var' = v

\* In eventual consistency, there's no ordering guarantee for reads. 
\* In the absence of any further writes, the replicas eventually converge.
ReadEventual(db, operation, var(_,_)) ==
    LET f == Filter(db, LAMBDA e: e.doc = operation.doc)
    IN IF f = <<>> THEN UNCHANGED var(FALSE, 1)
       ELSE \E v \in ({""} \cup {f[i].data : i \in 1..Len(f)}) : var(TRUE, v)

Read(db, operation, var(_,_)) ==
    /\ CASE Consistency = "Strong" -> ReadStrong(db, operation, var)
        \* [] Consistency = "Bounded_Staleness" -> -K..K
        \* [] Consistency = "Session" -> ReadSession(db, operation)
        \* [] Consistency = "Consistent_Prefix" -> Int
        [] Consistency = "Eventual" -> ReadEventual(db, operation, var)
        [] OTHER -> FALSE
    /\ db \o <<operation>>

Write(db, operation) ==
    db \o <<operation>>

================================================================================


Do not "return" a set of all possible values that the client has to handle non-deterministically. Instead, handle the non-determinism here.
Does it suffice to model atomic writes and reads 