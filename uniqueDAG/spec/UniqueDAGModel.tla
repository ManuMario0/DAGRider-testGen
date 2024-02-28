--------------------------- MODULE UniqueDAGModel ---------------------------

EXTENDS Apalache

\* @type: Int => Int;
ChooseLeader(i) == i

VARIABLES
    \* @type: Int -> Int -> $fullVertex;
    dag,
    \* @type: Seq(BLOCK);
    BlockSeq,
    \* @type: Int -> Int -> Int;
    ProcessState,
    \* @type: Int -> Int -> Seq(Int);
    commitWithRef,
    \* @type: Int -> Int;
    decidedWave,
    \* @type: Int -> Int -> {exists: Bool, edges: Set(Int)};
    leaderReachablity,
    \* @type: Int -> {current: Seq(Int), last: Seq(Int)};
    leaderSeq

INSTANCE UniqueDAGSpec WITH
    NumProcess <- 4,
    NumWaves <- 1,
    BlockSet <- Gen(5),
    ChooseLeader <- ChooseLeader,
    dag <- dag,
    ProcessState <- ProcessState,
    commitWithRef <- commitWithRef,
    decidedWave <- decidedWave,
    leaderReachablity <- leaderReachablity,
    leaderSeq <- leaderSeq

=============================================================================
\* Modification History
\* Last modified Wed Feb 28 15:43:13 AEDT 2024 by emmanuel
\* Created Wed Feb 28 08:44:58 AEDT 2024 by emmanuel
