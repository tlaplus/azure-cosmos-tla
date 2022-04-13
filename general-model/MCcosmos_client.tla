--------------------------- MODULE MCcosmos_client ----------------------------
EXTENDS cosmos_client, TLC, TLCExt

\* MaxNumOp ==
\*     Len(History) < 7

Inv ==
    \A r \in DOMAIN Database:
        \A i \in DOMAIN Database[r]:
            Database[r][i] = i-1

Level ==
    TLCGet("level") < 1000

Alias ==
    [
        db |-> [ i \in DOMAIN Database |-> Last(Database[i]) ]
    ]

Explore ==
    \* UNCHANGED vars
    \* ~ ENABLED Next
    \* PickSuccessor(42 + "")
    \* 42 + ""
    TRUE
    \* PickSuccessor(CosmosDB)

NoStutter ==
    vars # vars'
=============================================================================
\* Authored by Cosmos DB
