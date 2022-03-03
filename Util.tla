------- MODULE Util ------
EXTENDS Integers, Sequences

S1 == <<7,21,0,3,1,0,-1,-5>>

S2 == <<9,2,3,78,4,1,8,6,9,-4>>

RECURSIVE FoldSeq(_,_,_)
FoldSeq( Op(_,_), v, seq ) == IF seq = <<>>
                              THEN v
                              ELSE FoldSeq( Op, Op(v,Head(seq)), Tail(seq) )

FilterSeq(seq, cmp(_)) ==
    FoldSeq(LAMBDA acc, e: IF cmp(e) THEN acc \o <<e>> ELSE acc, <<>>, seq)

SortedSeq(sorted, e) == 
    FilterSeq(sorted, LAMBDA a: a < e) \o <<e>> \o FilterSeq(sorted, LAMBDA a: a > e)

Main ==
    FoldSeq(SortedSeq, <<>>, S1 \o S2)

=====
------- MODULE Util ------
EXTENDS Integers, Sequences, SequencesExt, FiniteSetsExt, Functions

S1 == <<7,21,0,3,1,0,-1,-5>>

S2 == <<9,2,3,78,4,1,8,6,9,-4>>


\* Merge2 ==
\*     LET U == Range(S1) \cup Range(S2)
\*     IN FoldSet(LAMBDA e, acc: acc \o <<e>>, <<>>, U)

\* Merge3 ==
\*     LET U == Range(S1) \cup Range(S2)
\*     IN CHOOSE f \in [ 1..Cardinality(U) -> U ] : 
\*             \A i,j \in DOMAIN f: i < j => f[i] < f[j]

FilterSeq(seq, cmp(_)) ==
    FoldLeft(LAMBDA acc, e: IF cmp(e) THEN acc \o <<e>> ELSE acc, <<>>, seq)

SortedSeq(sorted, e) == 
    FilterSeq(sorted, LAMBDA a: a < e) \o <<e>> \o FilterSeq(sorted, LAMBDA a: a > e)

Main ==
    FoldLeft(SortedSeq, <<>>, S1 \o S2)

====
\* f as a = [x | x <- as, x < a] ++ [a] ++ [x | x <- as, x >= a]
Sort(sorted, e) == 
    Filter(LAMBDA a: a < e) \o <<e>> \o Filter(LAMBDA a: a > e)

Merge ==
    Sort(<<>>, 42)

====

Merge ==
    FoldFunction(op(_,_), <<>>, S1)

=========