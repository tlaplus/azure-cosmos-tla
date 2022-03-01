------------------------- MODULE MCswscop -------------------------
EXTENDS swscop, TLC, IOUtils

mcNumClients ==
    1

mcMaxNumOp ==
    3

mcK ==
    2

------

mcConsistency ==
    IOEnv.mcConsistency

mcProperty ==
    IOEnv.mcProperty

mcEventual ==
    []\/ mcProperty # "Eventual"
      \/ Eventual

mcConsistent_Prefix ==
    []\/ mcProperty # "Consistent_Prefix"
      \/ Consistent_Prefix

mcSession ==
    []\/ mcProperty # "Session"
      \/ Session

mcBounded_Staleness ==
    []\/ mcProperty # "Bounded_Staleness"
      \/ Bounded_Staleness

mcStrong ==
    []\/ mcProperty # "Strong"
      \/ Strong

=============================================================================
