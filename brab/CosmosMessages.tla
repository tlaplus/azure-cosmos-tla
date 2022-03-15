---- MODULE CosmosMessages ----
EXTENDS Integers

Levels ==
    {"Strong", "Bounded_staleness", "Session", "Consistent_prefix", "Eventual"}

Consistency ==
    [level: Levels, lsn: Int] \* log-sequence-number (lsn)

CONSTANT Regions

CONSTANT WriteRegions

CONSTANT Clients

CONSTANT Null, Data

\* Request: Client -> Cosmos
Request ==
    [
        doc: STRING,     \* The document that was read.
        \* data: Data,      \* The data that was read.
        type: {"Read"}, 
        consistency: Consistency, 
        region: Regions, \* The region the original read request was sent to.
        orig: Clients    \* The client that originally sent the read request.
    ] \cup
    [
        doc: STRING,     \* The document that was written.
        data: Data,      \* The data that was written.
        old: Data \cup {Null},    \* If not Null, the expected data to be overriden (If-Match).  Note that If-Match & etags are essentially compare-and-swap.
        type: {"Write"}, 
        consistency: Consistency, 
        region: WriteRegions, \* The region the original write request was sent to.
        orig: Clients
    ]

\* Response: Cosmos -> Client
Response ==
    [
        doc: STRING,     \* The document that was written.
        data: Data,    \* "ACK", a session token, or the data that was read.
        type: {"Reply", "Error"}, 
        consistency: Consistency, 
        region: Regions, \* The region the original read request was sent to.
        orig: {"cosmos"}
    ] \cup 
    [
        doc: STRING,       \* The document that was written.
        data: Data \cup {Null},      \* Non-null if NACK because of If-Match.
        \* In case of error, the write might or might not have succeeded. An error
        \* models the case that the database response to a write request was lost.
        \* Message duplications is assumed to be prevented by the communicaion
        \* protocol (e.g. TCP).
        type: {"ACK", "NACK", "Error"},
        consistency: Consistency, 
        region: WriteRegions, \* The region the original read request was sent to.
        orig: {"cosmos"}
    ]

CRequest(doc, data, old, type, consistency, region, orig) ==
    [
        doc |-> doc, data |-> data, old |-> Null,
        type |-> type, consistency |-> consistency,
        region |-> region, orig |-> orig
    ]

CError(request) ==
    [
        doc |-> request.doc, data |-> Null,
        type |-> "Error", consistency |-> [level |-> request.consistency.level, lsn |-> -1],
        region |-> request.region, orig |-> "cosmos"
    ]

CReply(request, data, lsn) ==
    [
        doc |-> request.doc, data |-> data,
        type |-> "Reply", consistency |-> [level |-> request.consistency.level, lsn |-> lsn],
        region |-> request.region, orig |-> "cosmos"
    ]

CAck(request, lsn) ==
    [
        doc |-> request.doc, data |-> Null,
        type |-> "ACK", consistency |-> [level |-> request.consistency.level, lsn |-> lsn],
        region |-> request.region, orig |-> "cosmos"
    ]

CNack(request, data, lsn) ==
    [
        doc |-> request.doc, data |-> data,
        type |-> "NACK", consistency |-> [level |-> request.consistency.level, lsn |-> lsn],
        region |-> request.region, orig |-> "cosmos"
    ]
======