---- MODULE MCCosmosDB -----
EXTENDS CosmosDB

clients ==
    {"c1"}
        
data ==
    clients

regions ==
    {"R"}
        
MaxRequest ==
    \* /\ BagCardinality(inbox) < 5
    /\ Len(database) < 5

Level ==
    \* TRUE
    \* TLCGet("level") < 21
    Len(database) < 2
======