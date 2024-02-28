# DAG-Rider specification with only one DAG

The Idea of this specification is to only store one DAG (the view of the DAG from the network, that is the union of all of the local view of the DAGs) and only store locally the current processed round of each process.

## Assumption on the execution of the algorithm

For this to work, I need an assumption : whenever a process r\_bcast a vertex, then it r\_recv it and add it to it's local DAG (or drop it) before adding a new vertex. This ensure that every new vertex is connected to the vertex of the same process in a round before directly.
It seams like it is a reasonable thing to assume considering it is possible to implement and it only restrict the algorithm meaning the algorithm still implement the same properties (it is only a subset of all possible traces generated by the original algorithm).

Another assumption we're gonna do is that we do not dissociate the receiveing phase from the processing phase, limiting the amount of storage needed in the model. It does not change the general behaviour of the system since we can still choose the scheduling of the processing of each vertex, meaning once again we're only taking a subset of all possible traces of execution of the protocol.
