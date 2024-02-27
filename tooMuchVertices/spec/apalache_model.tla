--------------------------- MODULE apalache_model ---------------------------

EXTENDS Apalache, Integers

CONSTANTS(*
    \* type: Int;
    NumProcessors,
    
    \* type: Int;
    NumWaves,
    *)
    \* @type: Set(BLOCK);
    BlockSet

NumProcessors == 1
NumWaves == 1
ChooseLeader(i) == Guess(1..NumProcessors)

VARIABLE
    \* @type: Int -> Int -> Seq(Int);
    commitWithRef,
    \* @type: Int -> Int;
    decidedWave,
    \* @type: Int -> Int -> {exists: Bool, edges: Set(Int)};
    leaderReachablity,
    \* @type: Int -> {current: Seq(Int), last: Seq(Int)};
    leaderSeq,
    \* @type: Int -> Seq(BLOCK);
    blocksToPropose,
    \* @type: Int -> Set({sender: Int, inRound: Int, vertex: $vertex});
    broadcastNetwork,
    \* @type: Int -> Int -> Bool;
    broadcastRecord,
    \* @type: Int -> Set($vertex);
    buffer,
    \* @type: Int -> Int -> Int -> Int;
    dag,
    \* @type: Int -> Int;
    round

INSTANCE DAGRiderSpecification
WITH NumProcessors <- NumProcessors,
        NumWaves <- NumWaves,
        BlockSet <- BlockSet,
        ChooseLeader <- ChooseLeader,
        commitWithRef <- commitWithRef,
        decidedWave <- decidedWave,
        leaderReachablity <- leaderReachablity,
        leaderSeq <- leaderSeq,
        blocksToPropose <- blocksToPropose,
        broadcastNetwork <- broadcastNetwork,
        broadcastRecord <- broadcastRecord,
        buffer <- buffer,
        dag <- dag,
        round <- round
        
ConstInit == (*
    /\ NumProcessors = Gen(1)
    /\ NumWaves = Gen(1)
    /\ NumProcessors > 2
    /\ NumWaves > 2*)
    /\ BlockSet = Gen(1)

=============================================================================
\* Modification History
\* Last modified Mon Feb 26 17:26:07 AEDT 2024 by emmanuel
\* Created Sun Feb 25 12:08:18 AEDT 2024 by emmanuel
