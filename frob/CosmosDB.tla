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
ReadStrong(db, operation) ==
    LET f == Filter(db, LAMBDA e: e.doc = operation.doc)
    IN IF f = <<>> THEN {""} ELSE {Last(f).data}

\* consistent-prefix
\* monotonic reads
\* monotonic writes
\* read-your-writes
\* write-follows-reads guarantees
ReadSession(db, token, operation) ==
    LET f == Filter(SubSeq(db, token, Len(db)), LAMBDA e: e.doc = operation.doc)
    IN IF f = <<>> THEN {""} ELSE {Last(f).data}

\* In eventual consistency, there's no ordering guarantee for reads. 
\* In the absence of any further writes, the replicas eventually converge.
ReadEventual(db, operation) ==
    LET f == Filter(db, LAMBDA e: e.doc = operation.doc)
    IN IF f = <<>> THEN {""} ELSE {f[i].data : i \in 1..Len(f)}

Read(db, operation) ==
    CASE Consistency = "Strong" -> ReadStrong(db, operation)
        \* [] Consistency = "Bounded_Staleness" -> -K..K
        \* [] Consistency = "Session" -> ReadSession(db, operation)
        \* [] Consistency = "Consistent_Prefix" -> Int
        [] Consistency = "Eventual" -> ReadEventual(db, operation)

Write(db, operation) ==
    db \o <<operation>>

Session(db, operation) ==
    Len(db) + 1

================================================================================