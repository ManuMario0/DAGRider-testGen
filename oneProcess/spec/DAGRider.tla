------------------------------ MODULE DAGRider ------------------------------

EXTENDS Integers

CONSTANT
    \* @type: Number of process in the model
    NumProcess,
    \* @type: Number of waves of the execution
    NumWaves

\* defines some utility constants
ProcessSet ==
    1..NumProcess
    
NumRound ==
    4*NumWaves
 
RoundSet ==
    0..NumRound

VertexSet ==
    [
        process: ProcessSet,
        round: RoundSet
    ]

\* defines some vertex stuff for easier handling
(*
    @typeAlias: refVertex = [process: in, round: Int]
    @typeAlias: dagVertex = [block: BLOCK, weakedges: Set(refVertex), strongedges: Set(refVertex)]
    @typeAlias: fullVertex = [process: Int, round: Int, block: BLOCK, weakedges: Set(refVertex), strongedges: Set(refVertex)]
*)
NoneVertex ==
    [
        block: "NONE_OF_BLOCK",
        strongedges: {},
        weakedges: {}
    ]

\* Variables definition and initialisation

VARIABLES
    \* @type: Int -> Int -> $vertex
    dag,
    \* @type: Seq(BLOCK)
    blocksToPropose,
    \* @type: Int
    round
    
InitDag ==
    dag = [p \in ProcessSet |-> [r \in RoundSet |-> NoneVertex]]
    
InitBlocksToPropose ==
    blocksToPropose = <<>>
   
InitRound ==
    round = 0
    
    
    
    
\* Set of functions of the algorithm
Path(v, u) ==
    \E k \in RoundSet: \E s \in [1..k -> VertexSet]:
         /\ v = s[1]
         /\ u = s[k]
         /\ \A i \in 2..k:
            /\ dag[s[i].process][s[i].round].block # "NONE_OF_BLOCK"
            /\ s[i] \in s[i-1].strongedges \cup s[i-1].weakedges
            
StrongPath(v, u) ==
    \E k \in RoundSet: \E s \in [1..k -> VertexSet]:
         /\ v = s[1]
         /\ u = s[k]
         /\ \A i \in 2..k:
            /\ dag[s[i].process][s[i].round].block # "NONE_OF_BLOCK"
            /\ s[i] \in s[i-1].strongedges



CreateVertex(p, r) ==
    dag' = [dag EXCEPT ![p][r] = [
        block |-> "1_OF_BLOCK", (*Head(BlockSeq), *)
        strongedges |->
            {[round |-> r-1, source |-> q] :
                q \in {i \in ProcessSet : dag[i][r-1].block # "NONE_OF_BLOCK"}},
        weakedges |->
            {[round |-> tmpr, source |-> q] :
                q \in {i \in ProcessSet : ProcessState[p][i] < r-1} }
        ]]

\* Possible actions
NextRoundTn(p) ==  
   /\ NextRoundCond(p)
   /\ CreateVertex(p, ProcessState[p][p]+1)
   
AddVertexTn(p, v) == 
   (* Check that the vertex is actually valid *)
   /\ dag[v.source][v.round].block /= "NONE_OF_BLOCK"
   (* Check that the round of the vertex is less than the vertex we want *)
   /\ v.round <= ProcessState[p][p]
   (* Check that we did not have already process this vertex *)
   /\ ProcessState[p][v.source] < v.round
   (* Check that all the vertex it is connected to are already in the local DAG *)
   /\ \A link \in (dag[v.source][v.round].strongedges \cup dag[v.source][v.round].weakedges) :
        ProcessState[p][link.source] >= link.round
   (* Update our local view of the DAG *)
   /\ ProcessState' = [ProcessState EXCEPT ![p][v.source] = v.round]
   /\ UNCHANGED <<dag>>



=============================================================================
\* Modification History
\* Last modified Thu Mar 07 14:48:26 AEDT 2024 by emmanuel
\* Created Wed Mar 06 11:04:57 AEDT 2024 by emmanuel
