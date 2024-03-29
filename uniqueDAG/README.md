# DAG-Rider specification with only one DAG

The Idea of this specification is to only store one DAG (the view of the
DAG from the network, that is the union of all of the local view of the
DAGs) and only store locally the current processed round of each process.

## Assumption on the execution of the algorithm

For this to work, I need an assumption : whenever a process r\_bcast a vertex,
then it r\_recv it and add it to it's local DAG (or drop it) before adding
a new vertex. This ensure that every new vertex is connected to the vertex
of the same process in a round before directly.
It seams like it is a reasonable thing to assume considering it is possible
to implement and it only restrict the algorithm meaning the algorithm still
implement the same properties (it is only a subset of all possible traces
generated by the original algorithm).

Another assumption we're gonna do is that we do not dissociate the receiveing
phase from the processing phase, limiting the amount of storage needed in the
model. It does not change the general behaviour of the system since we can
still choose the scheduling of the processing of each vertex, meaning once
again we're only taking a subset of all possible traces of execution of the
protocol.

## How to use

For usage, you'll need to have installed one of the folowings :
- [Apalache](https://apalache.informal.systems)
- [TLA+ toolbox](https://lamport.azurewebsites.net/tla/tla.html)

### Launching model-checking

For model-checking with apalache, the command is the following :
```bash
apalache-mc check --length=7 --inv=Inv path_to_UniwueDAGModel.tla
```

where the length is the number of steps for which the model-checking will be run.

You can customize the model in `path_to_UniwueDAGModel.tla` by changing the
different parameters.

For TLC, it is much simpler. Just open the file UniqueDAGSpec.tla with the toolbox
and go to models and you should be able to set everything up correctly like the
invariant to check and the values of the different constants.
For a more efficient execution, disable the profiling in `Additional TLC Options`.

### Launching simulate

For simulate mode in apalache, this is the same command where you replace the `check`
with `simulate`.

For simulate mode in TLC, you can use the script `autogentests.sh` in the `tools`
folder. For this, just locate the `tla2tools.jar` file (it should be in a
folder named Eclipse comming with the TLA+ toolbox), and write
```bash
export TLAEclipseDir=/path/to/tla2tools/folder/
```

and then run the tool on the example file with :
```bash
./autogentests.sh ../config.gentest
```

The file `config.gentest` contains a list of paramters to generates tests automatically.
An entry in the file usually looks like the following :
```
Name?AtLeast9Rounds;Count?10;NumProcess?7;NumWaves?3;Depth?400;Inv?\\A p \\in ProcessSet : ProcessState[p][p] <= 9;Constraints?TRUE
```

Where you can set several parameters for each tests :
- Name : the name of the test
- Count : the number of tests we generates with those settings
- NumProcess : the number of process for the tests
- NumWaves : the number of waves for the test
- Depth : the maximum number of steps you're looking into to invalidate the invariant
- Inv : the invariant that you want to find a counter example of
- Constraints : the constraints you add to the model to orient the search of the \
counter example

Remark : currently this tool is not generating actual tests but only the traces of
exectution for now.
