---- MODULE SmokeCosmosDB -----
EXTENDS MCCosmosDB, FiniteSets, SmokeTests

TestInit ==
    /\ session = 1
    /\ pc = [ c \in Clients |-> "read" ]
    /\ client = [ c \in Clients |-> Null ]
    /\ outbox = [ c \in Clients |-> <<>> ]
    /\ inbox = <<>>
    \* Initially, the database is modeled to be not-empty, but to contain some
    \* data.
    /\ database \in [ {1} -> [
                            consistency: [level: {"Strong"}, lsn: 1..1], 
                            data: {1}, doc: {"doc1"}, old: {Null}, 
                            orig: Clients, region: Regions, type: {"Write"}
                             ]
                    ] \cup {<<>>}

TestNextNonEmpty ==
    /\ database # <<>>
    /\ UNCHANGED vars
    \* Write|Strong|No If-Match
    /\ LET responses == WriteResponse(CRequest("doc1", 2, Null, "Write", [level |-> "Strong", lsn |-> 0], "R", "c1"))
       IN /\ Cardinality(responses) = 2
          /\ \A res \in responses:
                /\ res \in Response
                /\ res.doc = "doc1"
                /\ res.type \in {"ACK", "Error"}
                /\ res.type = "ACK" => 
                    /\ res.data = 2
                    \* TODO: lsn = 2 even though WriteResponse leaves the database variable unchanged.
                    \* TODO: The database var is updated in the definition CosmosWrite, which is built
                    \* TODO: from WriteResponse.
                    /\ res.consistency = [level |-> "Strong",lsn |-> 2]
                /\ res.type = "Error" => 
                    /\ res.data = Null
                    /\ res.consistency = [level |-> "Strong",lsn |-> -1]
                /\ res.region = "R"
                /\ res.orig = "cosmos"
    \* Write|Strong|If-Match that is expected to fail
    /\ LET responses == WriteResponse(CRequest("doc1", 3, 2, "Write", [level |-> "Strong", lsn |-> 0], "R", "c1"))
       IN /\ Cardinality(responses) = 2
          /\ \A res \in responses:
                /\ res \in Response
                /\ res.doc = "doc1"
                /\ res.type \in {"NACK", "Error"}
                /\ res.type = "NACK" => 
                        /\ res.consistency = [level |-> "Strong",lsn |-> 1]
                        /\ res.data = 1
                /\ res.type = "Error" =>
                        /\ res.consistency = [level |-> "Strong",lsn |-> -1]
                        /\ res.data = Null
                /\ res.region = "R"
                /\ res.orig = "cosmos"
    \* Write|Strong|If-Match that is expected to succeed
    /\ LET responses == WriteResponse(CRequest("doc1", 2, 1, "Write", [level |-> "Strong", lsn |-> 0], "R", "c1"))
       IN /\ Cardinality(responses) = 2
          /\ \A res \in responses:
                /\ res \in Response
                /\ res.doc = "doc1"
                /\ res.type \in {"ACK", "Error"}
                /\ res.type = "ACK" => 
                        /\ res.consistency = [level |-> "Strong",lsn |-> 2]
                        /\ res.data = 2
                /\ res.type = "Error" =>
                        /\ res.consistency = [level |-> "Strong",lsn |-> -1]
                        /\ res.data = Null
                /\ res.region = "R"
                /\ res.orig = "cosmos"
    \* Read|Strong
    /\ LET responses == ReadResponse(CRead("doc1", [level |-> "Strong", lsn |-> 0], "R", "c1"))
       IN /\ Cardinality(responses) = 2
          /\ \A res \in responses:
                /\ res \in Response
                /\ res.doc = "doc1"
                /\ res.type \in {"Reply", "Error"}
                /\ res.type = "Reply" => 
                        /\ res.consistency = [level |-> "Strong",lsn |-> 1]
                        /\ res.data = 1
                /\ res.type = "Error" =>
                        /\ res.consistency = [level |-> "Strong",lsn |-> -1]
                        /\ res.data = Null
                /\ res.region = "R"
                /\ res.orig = "cosmos"

TestNextEmpty ==
    /\ database = <<>>
    /\ UNCHANGED vars
     \* Read|Strong|Empty DB
    /\ LET responses == ReadResponse(CRead("doc1", [level |-> "Strong", lsn |-> 0], "R", "c1"))
       IN /\ Cardinality(responses) = 1
          /\ \A res \in responses:
                /\ res \in Response
                /\ res.doc = "doc1"
                /\ res.type \in {"Error"}
                /\ res.type = "Error" =>
                        /\ res.consistency = [level |-> "Strong",lsn |-> -1]
                        /\ res.data = Null
                /\ res.region = "R"
                /\ res.orig = "cosmos"

TestNext ==
    \/ TestNextNonEmpty
    \/ TestNextEmpty
======