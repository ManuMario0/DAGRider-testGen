--------------------------- MODULE UniqueDAGSpec ---------------------------

(*                                                                         *)
(* DAG-Rider specification addapted for model checking.                    *)

EXTENDS FiniteSets,
        Integers,
        Sequences

-----------------------------------------------------------------------------

(*---------------------------------ALIASES---------------------------------*)

(*
    @typeAlias: lightVertex = {
        round: Int,
        source: Int
    };
*)
LightVertex_typedefs == TRUE

(*
    @typeAlias: fullVertex = {
        block : BLOCK,
        strongedges : Set($lightVertex),
        weakedges : Set($lightVertex),
        reachableleaders : Set(Int)
    };
*)
FullVertex_typedefs == TRUE

(*--------------------------------CONSTANTS--------------------------------*)

(* NumProcessors is the number of participating processes in the protocol. *)
(* We assume this is non zero. We number processes 1 to NumProcessors,     *)
(* and define ProcessorSet as the set of participating processes.          *) 
(* We define maximum allowed process failures (NumFaultyProcessors) as the *)
(* greatest integer less than one third of the total number of processes.  *)

CONSTANT
    \* @type: Int;
    NumProcess

ASSUME NumProcessorAsm == 
   NumProcess \in Nat\{0}

NumFaultyProcessors == 
   (NumProcess-1) \div 3

ProcessSet == 
   1..NumProcess

-----------------------------------------------------------------------------

(* NumWaves is the number of waves after which the protocol will stop, we  *)
(* assume this is non zero. We number waves from 1 to NumWaves and define  *)
(* WaveSet as the set of waves. A wave consists of 4 rounds. We define     *)
(* RoundSet as set of rounds along with an initial round 0.                *)

CONSTANT
    \* @type: Int;
    NumWaves

ASSUME NumWaveAsm == 
   NumWaves \in Nat\{0}

WaveSet == 
   1..NumWaves

RoundSet == 
   0..(4*NumWaves)

-----------------------------------------------------------------------------

(* BlockSet is a set of blocks that can be proposed by participating proc- *)
(* esses.                                                                  *)

CONSTANT
    \* @type: Seq(BLOCK);
    BlockSet

-----------------------------------------------------------------------------

(* ChooseLeader(_) is function that maps WaveSet to ProcessorSet.          *)

CONSTANT
    \* @type: Int => Int;
    ChooseLeader(_)

-----------------------------------------------------------------------------

(* Definition of the global DAG (that is, the network-view of the DAG.     *)

VARIABLE
    \* @type: Int -> Int -> $fullVertex;
    dag
    
NoneBlock ==
    [block |-> "NONE_OF_BLOCK",
     strongedges |-> {},
     weakedges |-> {},
     reachableleaders |-> {}]
    
InitDag ==
    dag = [p \in ProcessSet |->
            [r \in RoundSet |->
                NoneBlock
            ]
          ]

-----------------------------------------------------------------------------

(* Definition of blocksToPropose                                           *)

VARIABLE
    \* @type: Seq(BLOCK);
    BlockSeq
    
InitBlockSeq ==
    BlockSeq = BlockSet

-----------------------------------------------------------------------------

(* Definition of processState                                              *)

VARIABLE
    \* @type: Int -> Int -> Int;
    ProcessState

InitProcessState ==
    ProcessState = [p \in ProcessSet |-> [q \in ProcessSet |-> 0] ]

-----------------------------------------------------------------------------

(* Since DAGRiderSpecification extends LeaderConsensusSpecification, we    *)
(* additionally have the four variables (commitWithRef, decidedWave,       *)
(* leaderReachablity, leaderSeq) from the LeaderConsensusSpecification.    *)

VARIABLE
    \* @type: Int -> Int -> Seq(Int);
    commitWithRef,
    \* @type: Int -> Int;
    decidedWave,
    \* @type: Int -> Int -> {exists: Bool, edges: Set(Int)};
    leaderReachablity,
    \* @type: Int -> {current: Seq(Int), last: Seq(Int)};
    leaderSeq

-----------------------------------------------------------------------------

LeaderConsensus == 
   INSTANCE LeaderConsensusSpecification
   WITH NumWaves <- NumWaves,
        NumProcessors <- NumProcess,
        commitWithRef <- commitWithRef,
        decidedWave <- decidedWave,
        leaderReachablity <- leaderReachablity,
        leaderSeq <- leaderSeq

(*-------------------------STATE-TRANSITIONS-------------------------------*)

(* Transition ProposeTn(p, b) encodes process p proposing block b.         *)
(*
\* type: Int => Bool;
ProposeTn(p) == 
   /\ Len(BlockSeq) > 0
   /\ BlocksToPropose' = [BlocksToPropose EXCEPT 
         ![p] = Append(BlocksToPropose[p], Head(BlockSeq))]
   /\ BlockSeq' = Tail(BlockSeq)
   /\ UNCHANGED <<dag, ProcessState>>
   /\ UNCHANGED LeaderConsensus!vars*)

-----------------------------------------------------------------------------

(* Transition NextRoundTn(p) encodes process p moving to the next round of *)
(* DAG construction.  Upon completion of the current round process p moves *)
(* to the next round by creating (CreateVertex) and broadcasting (Broadcast*)
(* a new vertex. Additionally, when next round leads to a new wave it tries*)
(* to decide the current wave (ReadyWave), if decide condition is satisfied*)
(* it takes UpdateDecidedWaveTn in LeaderConsensus.                        *)

(* TODO: the reacheable leader part is not complete *)
\* @type: (Int, Int) => Bool;
CreateVertex(p, r) ==
    /\ dag' = [dag EXCEPT ![p][r] = [
        block |-> Head(BlockSeq), 
        strongedges |->
            {[round |-> r-1, source |-> q] :
                q \in {i \in ProcessSet : ProcessState[p][i] >= r-1}},
        weakedges |->
            {[round |-> ProcessState[p][q], source |-> q] :
                q \in {i \in ProcessSet : ProcessState[p][i] < r-1} },
        reachableleaders |->
            UNION { dag[q][r-1].reachableleaders :
                q \in { i \in ProcessSet : ProcessState[p][i] >= r-1 } }
            \cup
            IF (r % 4) = 1 /\ ChooseLeader((r+3) \div 4) = p
            THEN { (r+3) \div 4 }
            ELSE {}
        ]]
    /\ ProcessState' = [ProcessState EXCEPT ![p][p] = r]

\* @type: (Int, Int) => Bool;
ReadyWave(p, w) == 
   IF ( (* Check wether the wave vertex leader is in the dag of the process *)
        /\ ProcessState[p][ChooseLeader(w)] >= 4*w-3
        (* Check that we have enough vertex to commit the wave *)
        /\  Cardinality(
                { s \in ProcessSet :
                    ProcessState[p][s] >= 4*w
                    /\ w \in dag[p][4*w].reachableleaders }
            ) > 2*NumFaultyProcessors
   )
   THEN LeaderConsensus!UpdateDecidedWaveTn(p, w)
   ELSE UNCHANGED LeaderConsensus!vars

\* @type: Int => Bool;
NextRoundTn(p) ==  
   /\ ProcessState[p][p]+1 \in RoundSet
   /\ Cardinality({ q \in ProcessSet : ProcessState[p][q] >= ProcessState[p][p] })
        > 2*NumFaultyProcessors
   /\ CreateVertex(p, ProcessState[p][p]+1)
   /\ BlockSeq' = Tail(BlockSeq)
   /\ BlockSeq # <<>>
   /\ IF ProcessState[p][p]>0 /\ (ProcessState[p][p] % 4) = 0 
      THEN ReadyWave(p, (ProcessState[p][p] \div 4)) 
      ELSE UNCHANGED LeaderConsensus!vars

-----------------------------------------------------------------------------

(* Transition AddVertexTn(p, v) encodes process p adding  vertex v from the*)
(* buffer to the DAG. Additionally, if v is a leader vertex of some wave   *)
(* then UpdateWaveTn is performed on LeaderConsensus. For this update, we  *)
(* compute set of waves whose leader vertex in p, is in strong causal      *)
(* history of v (ReachableWaveLeaders).                                    *)

\* @type: (Int, $lightVertex) => Bool;
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
   (* Update our local LeaderGraph *)
   /\ IF v.round % 4 = 1 /\ v.source = ChooseLeader((v.round \div 4)+1)
      THEN LeaderConsensus!UpdateWaveTn(
            p,
            (v.round \div 4)+1,
            dag[v.source][v.round].reachableleaders
      )
      ELSE UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<dag, BlockSeq>>

-----------------------------------------------------------------------------

Init ==
    /\ InitDag
    /\ InitBlockSeq
    /\ InitProcessState
    /\ LeaderConsensus!Init
    
Next ==
    \E p \in ProcessSet, q \in ProcessSet :
    (*\/ ProposeTn(p)*)
    \/ NextRoundTn(p)
    \/ AddVertexTn(p, [round |-> ProcessState[p][q]+1, source |-> q])

Inv ==
    \A p \in ProcessSet, q \in ProcessSet :
        ProcessState[p][q] <= 1

=============================================================================
\* Modification History
\* Last modified Wed Feb 28 15:44:28 AEDT 2024 by emmanuel
\* Created Wed Feb 28 08:18:24 AEDT 2024 by emmanuel