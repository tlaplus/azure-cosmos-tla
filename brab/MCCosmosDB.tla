---- MODULE MCCosmosDB -----
EXTENDS CosmosDB

clients ==
    {"c1", "c2"}
        
data ==
    STRING

regions ==
    {"R"}
        
MaxRequest ==
    \* /\ BagCardinality(inbox) < 5
    /\ Len(database) < 10

Level ==
    \* TRUE
    \* TLCGet("level") < 21
    Len(database) < 10
    
======