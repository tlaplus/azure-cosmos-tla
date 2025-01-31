# A minimal model of Cosmos DB's behavior at different consistency levels for single read/writes

This collection of specifications is centered around `CosmosDB.tla`, which is a modular TLA+ specification of Cosmos DB's behavior for single reads and writes.
It can be re-used when modeling services that depend on Cosmos DB, as demonstrated in the `show*.tla` series of specifications.

The specification does not explicitly mention servers, clients, replication, regions, or other implementation details.
Instead, it abstractly specifies allowed behavior for any combination of clients, servers, and regions.
It also abstracts away all supported failure modes, ranging from spurious communication failure to multiple region failures.
It also abstracts away from communication: allowed behavior is specified in terms of "what any server is allowed to respond to a client request at this exact moment", representing a global view of any server.

To demonstrate the variety of edge cases and counter-intuitive behaviors our specification covers, `AnomaliesCosmosDB.tla` lists a set of regression tests that describe unusual scenarios that must be reachable by our model.
PRs increasing this set with new possibilities, including potentially failing cases that show limitations in our model, are of interest and welcome.

If you need to consider network delay in addition to Cosmos DB's base semantics (although it may not make a meaningful difference in most cases, and may complicate your model), `CosmosDBClient.tla` contains definitions that can be used to do this.

For examples of how to use the specifications here in order to model a specific situation, the files `show*.tla` contain variations of a model of the same [outage at Microsoft Azure](https://portal.microsofticm.com/imp/v3/incidents/postmortem/521677).
The spec [show521677simple.tla](https://github.com/tlaplus/azure-cosmos-tla/blob/master/simple-model/show521677simple.tla) models the outage *above* the network layer, while [show521677.tla](https://github.com/tlaplus/azure-cosmos-tla/blob/master/simple-model/show521677.tla) is more detailed and includes network communication (you can [interactively create and explore traces of the spec](https://will62794.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Ftlaplus%2Fazure-cosmos-tla%2Frefs%2Fheads%2Fmaster%2Fsimple-model%2Fshow521677.tla&constants%5BStrongConsistency%5D=%22Strong%22&constants%5BBoundedStaleness%5D=%22Bounded%22&constants%5BSessionConsistency%5D=%22SessionCon%22&constants%5BConsistentPrefix%5D=%22ConPre%22&constants%5BEventualConsistency%5D=%22Event%22&constants%5BVersionBound%5D=1&constants%5BStalenessBound%5D=1) with tla-web).  Similarly, two PlusCal specifications model the outage at the same two levels of abstraction ([show521677simplePCal](https://github.com/tlaplus/azure-cosmos-tla/blob/master/simple-model/show521677simplePCal.tla) and [show521677PCal.tla](https://github.com/tlaplus/azure-cosmos-tla/blob/master/simple-model/show521677PCal.tla)).
Model checking each spec with TLC will provide a counter-example which represents the root cause of the relevant outage.

## Analysis-specific files

Beyond re-usable components and edge case regression tests, this folder also contains records of our analysis and validation work.

- `*.cfg` are configuration files, which store additional information regarding what TLC should do with the corresponding `*.tla` files.
- `*Refine*.tla` represent verifications that behavior at different consistency levels represents a refinement ([in the model checking sense](https://www.hillelwayne.com/post/refinement/)) of behavior at other consistency levels.
- `RefineGeneralModel.tla` similarly checks refinement between `CosmosDB.tla` and the `general-model` sibling folder. It verifies that our model describes a superset of the behaviors allowed by `general-model`.
- `CosmosDBWithReads.tla` and `CosmosDBWithAllReads.tla` extend `CosmosDB.tla` with the assumption of arbitrary read and write operations, in two variants. For modularity, `CosmosDB.tla` itself has no state space and can be configured to only explore a limited set of specific operations.
For refinement and verifying properties however, we want to talk about "in all possible situations", and so we want to make TLC explore all possible operations (up to some bound).
`AllReads` and `Reads` differ in that `AllReads` will perform all possible read operations at all allowed read consistency levels all the time, whereas `Reads` is limited to a single read consistency level that is kept in an effectively-constant state variable. `Reads` is used by the `*Refine*.tla` tests, whereas `AllReads` is used by other analyses like `AnomaliesCosmosDB.tla`.
- `CosmosDBProps.tla` describes all the formal properties we want to verify for `CosmosDB.tla`, except one linearizability property of strongly consistent reads.
- `CosmosDBLinearizability.tla` describes a specific linearizability argument for strongly consistent reads. Model checking for this property is done as a refinement, which requires custom state space exploration and therefore cannot be batched together with the other properties.
- `MC*.tla` are utility files that contain model checking-specific definitions to help TLC work with the corresponding files without the `MC` prefix. To run model checking, give TLC the `MC`-prefixed file if there is one.
