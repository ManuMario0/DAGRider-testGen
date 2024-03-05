--------------------------- MODULE UniqueDAGSpec ---------------------------

(*                                                                         *)
(* DAG-Rider specification addapted for model checking.                    *)

EXTENDS FiniteSets,
        Integers,
        Sequences,
        TLAPS,
        TLC

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

(*-------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------*)
(*----------------------------OLD SPECIFICATION----------------------------*)
(*-------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------*)

-----------------------------------------------------------------------------

(*--------------------------------CONSTANTS--------------------------------*)

(* NumProcessors is the number of participating processes in the protocol. *)
(* We assume this is non zero. We number processes 1 to NumProcessors,     *)
(* and define ProcessorSet as the set of participating processes.          *) 
(* We define maximum allowed process failures (NumFaultyProcessors) as the *)
(* greatest integer less than one third of the total number of processes.  *)

CONSTANT NumProcessors

ASSUME NumProcessorAsm == 
   NumProcessors \in Nat\{0}

NumFaultyProcessors == 
   (NumProcessors-1) \div 3

ProcessorSet == 
   1..NumProcessors

ASSUME ProcSetAsm == 
   "History" \notin ProcessorSet

-----------------------------------------------------------------------------

(* NumWaves is the number of waves after which the protocol will stop, we  *)
(* assume this is non zero. We number waves from 1 to NumWaves and define  *)
(* WaveSet as the set of waves. A wave consists of 4 rounds. We define     *)
(* RoundSet as set of rounds along with an initial round 0.                *)

CONSTANT NumWaves

ASSUME NumWaveAsm == 
   NumWaves \in Nat\{0}

WaveSet == 
   1..NumWaves

RoundSet == 
   0..(4*NumWaves)

-----------------------------------------------------------------------------

(* BlockSet is a set of blocks that can be proposed by participating proc- *)
(* esses.                                                                  *)

CONSTANT BlockSet

-----------------------------------------------------------------------------

(* ChooseLeader(_) is function that maps WaveSet to ProcessorSet.          *)

CONSTANT ChooseLeader(_)

-----------------------------------------------------------------------------

(* Since we have bounded the number waves, there is a finite set of verti- *)
(* ces (VertexSet), which can be created by the participating processes.   *)
(* To define VertexSet, we first define ZeroRoundVertexSet (i.e., a set of *)
(* dummy vertices in round 0 of the DAG). Then, we define set              *)
(* UntilRoundVertex(r), which is set of vertices till round r. It is       *)
(* important to note that a vertex as defined in DAG-rider is not a vertex *)
(* but a rooted DAG (aka. downset). The downset stores the entire causal   *)
(* history of the node.                                                    *) 

ZeroRoundVertex(p) == 
   [round |-> 0, 
    source |-> p, 
    block |-> "Empty", 
    strongedges |-> {}, 
    weakedges |-> {}]

ZeroRoundVertexSet == 
   {ZeroRoundVertex(p) : p \in ProcessorSet}

RECURSIVE UntilRoundVertex(_)

UntilRoundVertex(r) == 
  IF r = 0
  THEN ZeroRoundVertexSet
  ELSE UntilRoundVertex(r-1) \cup [round : {r}, 
                                   source : ProcessorSet, 
                                   block : BlockSet, 
                                   strongedges : SUBSET(UntilRoundVertex(r-1)),
                                   weakedges : SUBSET(UntilRoundVertex(r-1))]  

VertexSet == UntilRoundVertex(4*NumWaves)

-----------------------------------------------------------------------------

(* When a vertex is broadcasted, the broadcast tags the vertex with its    *)
(* sender and the round in which it was sent. TaggedVertexSet is the set   *)
(* of all such tagged vertices.                                            *)

TaggedVertexSet == 
   [sender : ProcessorSet, inRound : RoundSet, vertex : VertexSet]

-----------------------------------------------------------------------------

(* NilVertex(p, r) is a vertex which represents the non-existence of a mes-*)
(* sage and whose block is Nil. To make the DAG more expressive we assume  *)
(* that DAG of every process has a vertex in every round created by every  *)
(* process. In practice, a process q might not have added a vertex created *)
(* by process p in round r in this case we assume that it has a Nil-       *)
(* Vertex(p, r).  We define NilVertexSet as the set of all nil vertices.   *)

NilVertex(p, r) == 
   [round |-> r,
    source |-> p,
    block |-> "Nil",
    strongedges |-> {},
    weakedges |-> {}]

NilVertexSet == 
   {NilVertex(p, r) : p \in ProcessorSet, r \in RoundSet}

-----------------------------------------------------------------------------

(*--------------------------STATE-VARIABLES--------------------------------*)

(* For every process p, blocksToPropose stores a sequence of blocks that   *)
(* are proposed but not yet initialized to order (blocks whose vertex is   *)
(* not yet created by the process).                                        *)

VARIABLE OLD_blocksToPropose

OLD_BlocksToProposeType == 
   OLD_blocksToPropose \in [ProcessorSet -> Seq(BlockSet)]

OLD_InitBlocksToPropose ==  
   OLD_blocksToPropose = [p \in ProcessorSet |-> <<>> ]

-----------------------------------------------------------------------------

(* For every process p, broadcastNetwork stores set of TaggedVertices that *)
(* are broadcasted but not yet received by p. Additionally it also stores  *)
(* history of all the TaggedVertices ever broadcasted on the network.      *)

VARIABLE OLD_broadcastNetwork

OLD_BroadcastNetworkType == 
   OLD_broadcastNetwork \in [ProcessorSet \cup 
                         {"History"} ->SUBSET(TaggedVertexSet)]

OLD_InitBroadcastNetwork == 
   OLD_broadcastNetwork = [p \in ProcessorSet \cup {"History"} |-> {}]

-----------------------------------------------------------------------------

(* For every process p and round r, broadcastRecord stores whether or not  *)
(* process p broadcasted a vertex in round r.                              *)

VARIABLE OLD_broadcastRecord

OLD_BroadcastRecordType == 
   OLD_broadcastRecord \in [ProcessorSet -> [RoundSet -> BOOLEAN]]

OLD_InitBroadcastRecord == 
   OLD_broadcastRecord = [p \in ProcessorSet |-> 
      [ r \in RoundSet |-> IF r = 0 THEN TRUE ELSE FALSE ]]

-----------------------------------------------------------------------------

(* For every process p, buffer stores set of vertices received by p via    *)
(* the broadcast.                                                          *)

VARIABLE OLD_buffer

OLD_BufferType == 
   OLD_buffer \in [ProcessorSet -> SUBSET(VertexSet)]

OLD_InitBuffer ==
   OLD_buffer = [p \in ProcessorSet |-> {}]

-----------------------------------------------------------------------------

(* For every process p, round r, process q, dag stores vertex in the DAG   *)
(* of process p created by process q in round r, if such a vertex does not *)
(* exists in the DAG then it stores NilVertex(q, r).                       *)

VARIABLE OLD_dag

OLD_DagType == 
   OLD_dag \in [ProcessorSet -> 
      [RoundSet  -> [ProcessorSet -> VertexSet \cup NilVertexSet]]]

OLD_InitDag == 
   OLD_dag = [p \in ProcessorSet |-> 
      [r \in RoundSet  |-> [q \in ProcessorSet |-> 
         IF r = 0 
         THEN ZeroRoundVertex(q) 
         ELSE NilVertex(q, r)]]]

-----------------------------------------------------------------------------

(* For every process p, round stores the round of DAG construction for     *)
(* process p.                                                              *) 

VARIABLE OLD_round

OLD_RoundType == 
   OLD_round \in [ProcessorSet -> RoundSet]

OLD_InitRound == 
   OLD_round = [p \in ProcessorSet |-> 0]

-----------------------------------------------------------------------------

(* Since DAGRiderSpecification extends LeaderConsensusSpecification, we    *)
(* additionally have the four variables (commitWithRef, decidedWave,       *)
(* leaderReachablity, leaderSeq) from the LeaderConsensusSpecification.    *)
(*
VARIABLE OLD_commitWithRef, 
         OLD_decidedWave,
         OLD_leaderReachablity,
         OLD_leaderSeq

-----------------------------------------------------------------------------

LeaderConsensus == 
   INSTANCE LeaderConsensusSpecification
   WITH NumWaves <- NumWaves,
        NumProcessors <- NumProcessors,
        commitWithRef <- OLD_commitWithRef,
        decidedWave <- OLD_decidedWave,
        leaderReachablity <- OLD_leaderReachablity,
        leaderSeq <- OLD_leaderSeq*)

-----------------------------------------------------------------------------

(*-------------------------STATE-TRANSITIONS-------------------------------*)

(* Before defining transitions we define some useful functions:            *)
(*  (1) Path(u, v): Boolean function that returns true if v is in causal   *)
(*      history of u.                                                      *)
(*  (2) StrongPath(u, v): Boolean function that returns true if v is in    *)
(*      strong causal history of u.                                        *)
(*  (3) InAddedVertex(p, r): Function on a system state. Returns added     *)
(*      vertices in round r of p's current DAG.                            *)
(*  (4) UntilAddedVertex(p, r): Function on a system state. Returns added  *)
(*      till round r of p's current DAG.                                   *)
(*  (5) NoPathVertices(p, r): Function on a system state. Returns set of   *)
(*      added vertices till round r of p's current DAG, which do not have  *)
(*      path from any of the added vertex in round r.                      *)
(*  (3) WaveLeader(p, w): Function on a system state. Returns p's leader   *)
(*      vertex of wave w.                                                  *)

RECURSIVE Path(_, _)
Path(u, v) == 
   IF u = v
   THEN TRUE
   ELSE IF u.round = 0
        THEN FALSE
        ELSE \E x \in u.weakedges \cup u.strongedges : Path(x, v)

RECURSIVE StrongPath(_, _)
StrongPath(u, v) == 
   IF u = v
   THEN TRUE
   ELSE IF u.round = 0
        THEN FALSE
        ELSE \E x \in u.strongedges : StrongPath(x, v)

InAddedVertex(p, r) == 
   {v \in VertexSet : v.round = r /\ OLD_dag[p][r][v.source] = v}

RECURSIVE UntilAddedVertex(_, _)

UntilAddedVertex(p, r) == 
   IF r = 0 
   THEN InAddedVertex(p, r)
   ELSE InAddedVertex(p, r) \cup UntilAddedVertex(p, r-1)

NoPathVertices(p, r) == {v \in UntilAddedVertex(p, r) : 
                         (\A w \in InAddedVertex(p, r) : ~Path(w,v))}                         

WaveLeader(p, w) == OLD_dag[p][4*w-3][ChooseLeader(w)]

-----------------------------------------------------------------------------

(* Transition ProposeTn(p, b) encodes process p proposing block b.         *)
(*
OLD_ProposeTn(p, b) == 
   /\ OLD_blocksToPropose' = [OLD_blocksToPropose EXCEPT 
         ![p] = Append(OLD_blocksToPropose[p], b)]
   /\ UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<OLD_broadcastNetwork, OLD_broadcastRecord, OLD_buffer, OLD_dag, OLD_round>>

-----------------------------------------------------------------------------

(* Transition NextRoundTn(p) encodes process p moving to the next round of *)
(* DAG construction.  Upon completion of the current round process p moves *)
(* to the next round by creating (CreateVertex) and broadcasting (Broadcast*)
(* a new vertex. Additionally, when next round leads to a new wave it tries*)
(* to decide the current wave (ReadyWave), if decide condition is satisfied*)
(* it takes UpdateDecidedWaveTn in LeaderConsensus.                        *)
*)
OLD_CreateVertex(p, r) == 
   [round |-> r, 
    source |-> p, 
    block |-> Head(OLD_blocksToPropose[p]), 
    strongedges |-> InAddedVertex(p, r-1),
    weakedges |-> NoPathVertices(p, r-1)]
(*
Broadcast(p, r, v) == 
   IF OLD_broadcastRecord[p][r] = FALSE
   THEN /\ OLD_broadcastRecord' = [OLD_broadcastRecord EXCEPT ![p][r] = TRUE]
        /\ OLD_broadcastNetwork' = [q \in ProcessorSet \cup {"History"} 
              |-> OLD_broadcastNetwork[q] \cup 
                  {[sender |-> p, inRound |-> r, vertex |-> v]}]
   ELSE UNCHANGED <<OLD_broadcastNetwork, OLD_broadcastRecord>>

ReadyWave(p, w) == 
   IF ( /\ OLD_dag[p][4*w-3][WaveLeader(p, w)] \in VertexSet 
        /\ \E Q \in SUBSET(InAddedVertex(p, 4*w)):
              /\ Cardinality(Q) > 2*NumFaultyProcessors 
              /\ \A u \in Q : StrongPath(u, WaveLeader(p, w)) )
   THEN LeaderConsensus!UpdateDecidedWaveTn(p, w)
   ELSE UNCHANGED LeaderConsensus!vars

OLD_NextRoundTn(p) ==  
   /\ OLD_round[p]+1 \in RoundSet
   /\ Cardinality(InAddedVertex(p, OLD_round[p])) > 2*NumFaultyProcessors
   /\ OLD_blocksToPropose[p] # <<>>
   /\ Broadcast(p, OLD_round[p]+1, OLD_CreateVertex(p, OLD_round[p]+1))
   /\ OLD_round' = [OLD_round EXCEPT ![p] = OLD_round[p]+1]
   /\ OLD_blocksToPropose' = [OLD_blocksToPropose EXCEPT 
         ![p] = Tail(OLD_blocksToPropose[p])]
   /\ IF OLD_round[p]>0 /\ (OLD_round[p] % 4) = 0 
      THEN ReadyWave(p, (OLD_round[p] \div 4)) 
      ELSE UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<OLD_buffer, OLD_dag>>

-----------------------------------------------------------------------------

(* Transition ReceiveVertexTn(p, q, r, v) encodes process p receiving      *)
(* vertex v created in round r by process q.                               *)

OLD_ReceiveVertexTn(p, q, r, v) == 
   /\ [sender |-> q, inRound |-> r, vertex |-> v] \in OLD_broadcastNetwork[p]
   /\ v.source = q
   /\ v.round = r
   /\ Cardinality(v.edges) > 2*NumFaultyProcessors
   /\ OLD_buffer' = [OLD_buffer EXCEPT ![p] = OLD_buffer[p] \cup {v}]
   /\ OLD_broadcastNetwork' = [OLD_broadcastNetwork EXCEPT 
         ![p] = OLD_broadcastNetwork[p] \ 
             {[sender |-> q, inRound |-> r, vertex |-> v]}]
   /\ UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<OLD_blocksToPropose, OLD_broadcastRecord, OLD_dag, OLD_round>>

-----------------------------------------------------------------------------

(* Transition AddVertexTn(p, v) encodes process p adding  vertex v from the*)
(* buffer to the DAG. Additionally, if v is a leader vertex of some wave   *)
(* then UpdateWaveTn is performed on LeaderConsensus. For this update, we  *)
(* compute set of waves whose leader vertex in p, is in strong causal      *)
(* history of v (ReachableWaveLeaders).                                    *)

ReachableWaveLeaders(p, v) == 
   {w \in WaveSet : StrongPath(v, WaveLeader(p, w))}

OLD_AddVertexTn(p, v) == 
   /\ v \in OLD_buffer[p]
   /\ v.round <= OLD_round[p]
   /\ OLD_dag[p][v.round][v.source] = NilVertex(v.source, v.round)
   /\ v.edges \in InAddedVertex(p, v.round -1)
   /\ OLD_dag'= [OLD_dag EXCEPT ![p][v.round][v.source] = v]
   /\ IF v.round % 4 = 1 /\ v.source = ChooseLeader((v.round \div 4)+1) 
      THEN LeaderConsensus!UpdateWaveTn(p, 
             (v.round \div 4)+1, ReachableWaveLeaders(p, v)) 
      ELSE UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<OLD_blocksToPropose, OLD_broadcastNetwork, 
                  OLD_broadcastRecord, OLD_buffer, OLD_round>>

-----------------------------------------------------------------------------


*)




(*-------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------*)
(*----------------------------NEW SPECIFICATION----------------------------*)
(*-------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------*)


(*--------------------------------CONSTANTS--------------------------------*)

(* NumProcessors is the number of participating processes in the protocol. *)
(* We assume this is non zero. We number processes 1 to NumProcessors,     *)
(* and define ProcessorSet as the set of participating processes.          *) 
(* We define maximum allowed process failures (NumFaultyProcessors) as the *)
(* greatest integer less than one third of the total number of processes.  *)
(*
CONSTANT
    \* @type: Int;
    NumProcess

ASSUME NumProcessorAsm == 
   NumProcess \in Nat\{0}

NumFaultyProcessors == 
   (NumProcess-1) \div 3

ProcessSet == 
   1..NumProcess*)

-----------------------------------------------------------------------------

(* NumWaves is the number of waves after which the protocol will stop, we  *)
(* assume this is non zero. We number waves from 1 to NumWaves and define  *)
(* WaveSet as the set of waves. A wave consists of 4 rounds. We define     *)
(* RoundSet as set of rounds along with an initial round 0.                *)
(*
CONSTANT
    \* @type: Int;
    NumWaves

ASSUME NumWaveAsm == 
   NumWaves \in Nat\{0}

WaveSet == 
   1..NumWaves

RoundSet == 
   0..(4*NumWaves)*)

-----------------------------------------------------------------------------

(* BlockSet is a set of blocks that can be proposed by participating proc- *)
(* esses.                                                                  *)
(*
CONSTANT
    \* @type: Seq(BLOCK);
    BlockSet*)

-----------------------------------------------------------------------------

(* ChooseLeader(_) is function that maps WaveSet to ProcessorSet.          *)
(*
CONSTANT
    \* @type: Int => Int;
    ChooseLeader(_)*)

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
    dag = [p \in ProcessorSet |->
            [r \in RoundSet |->
                NoneBlock
            ]
          ]

-----------------------------------------------------------------------------

(* Definition of blocksToPropose                                           *)
(*
VARIABLE
    \* type: Seq(BLOCK);
    BlockSeq
    
InitBlockSeq ==
    BlockSeq = CHOOSE y \in Seq(BlockSet) : TRUE*)

-----------------------------------------------------------------------------

(* Definition of processState                                              *)

VARIABLE
    \* @type: Int -> Int -> Int;
    ProcessState

InitProcessState ==
    ProcessState = [p \in ProcessorSet |-> [q \in ProcessorSet |-> 0] ]

(*-------------------------STATE-TRANSITIONS-------------------------------*)

-----------------------------------------------------------------------------

(* Transition NextRoundTn(p) encodes process p moving to the next round of *)
(* DAG construction.  Upon completion of the current round process p moves *)
(* to the next round by creating (CreateVertex) and broadcasting (Broadcast*)
(* a new vertex. Additionally, when next round leads to a new wave it tries*)
(* to decide the current wave (ReadyWave), if decide condition is satisfied*)
(* it takes UpdateDecidedWaveTn in LeaderConsensus.                        *)

\* @type: (Int, Int) => Bool;
CreateVertex(p, r, b) ==
    /\ dag' = [dag EXCEPT ![p][r] = [
        block |-> b,
        strongedges |->
            {[round |-> r-1, source |-> q] :
                q \in {i \in ProcessorSet : ProcessState[p][i] >= r-1}},
        weakedges |->
            {[round |-> ProcessState[p][q], source |-> q] :
                q \in {i \in ProcessorSet : ProcessState[p][i] < r-1} },
        reachableleaders |->
            UNION { dag[q][r-1].reachableleaders :
                q \in { i \in ProcessorSet : ProcessState[p][i] >= r-1 } }
            \union (
                IF (r % 4) = 1 /\ ChooseLeader((r+3) \div 4) = p
                THEN { (r+3) \div 4 }
                ELSE {}
            )
        ]]
    /\ ProcessState' = [ProcessState EXCEPT ![p][p] = r]

NextRoundCond(p) ==
    /\ ProcessState[p][p]+1 \in RoundSet
    /\ Cardinality({ q \in ProcessorSet : ProcessState[p][q] >= ProcessState[p][p] })
        > 2*NumFaultyProcessors
    (*/\ BlockSeq # <<>>*)

\* @type: Int => Bool;
NextRoundTn(p, b) ==  
   /\ NextRoundCond(p)
   /\ CreateVertex(p, ProcessState[p][p]+1, b)
   (*/\ BlockSeq' = Tail(BlockSeq)
   /\ IF ProcessState[p][p]>0 /\ (ProcessState[p][p] % 4) = 0 
      THEN ReadyWave(p, (ProcessState[p][p] \div 4)) 
      ELSE UNCHANGED <<decidedWave, commitWithRef, leaderReachablity, leaderSeq>>*)

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
   (* Update our local LeaderGraph *) (*
   /\ IF v.round % 4 = 1 /\ v.source = ChooseLeader((v.round+3) \div 4)
      THEN LeaderConsensus!UpdateWaveTn(
            p,
            (v.round+3) \div 4,
            dag[v.source][v.round].reachableleaders \ {(v.round+3) \div 4}
      )
      ELSE UNCHANGED <<decidedWave, commitWithRef, leaderReachablity, leaderSeq>>*)
   /\ UNCHANGED <<dag>>

-----------------------------------------------------------------------------

Init ==
    /\ InitDag
    (*/\ InitBlockSeq*)
    /\ InitProcessState
    (*/\ LeaderConsensus!Init*)

(* This means we always priorities the block submission *)
Next == 
         IF \E p \in ProcessorSet : NextRoundCond(p)
         THEN \E p \in ProcessorSet :
            LET b == CHOOSE b \in BlockSet: TRUE IN
            /\ NextRoundTn(p, b)
            /\ (* First step : adding the BLOCK to be broadcasted *)
               LET tmp_OLD_blocksToPropose == [OLD_blocksToPropose EXCEPT 
                    ![p] = Append(OLD_blocksToPropose[p], b)] IN
            
               (* Second step : creating and broadcast the vertex *)
               LET r == OLD_round[p]+1 IN
               LET v == OLD_CreateVertex(p, OLD_round[p]+1) IN
               LET tmp1_OLD_blocksToPropose == [tmp_OLD_blocksToPropose EXCEPT ![p] = Tail(tmp_OLD_blocksToPropose[p])] IN
               LET tmp1_OLD_broadcastNetwork ==
                    IF OLD_broadcastRecord[p][r] = FALSE
                    THEN [q \in ProcessorSet \cup {"History"}
                            |-> OLD_broadcastNetwork[q] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}]
                    ELSE OLD_broadcastNetwork
               IN
               LET tmp1_OLD_broadcastRecord ==
                    IF OLD_broadcastRecord[p][r] = FALSE
                    THEN [OLD_broadcastRecord EXCEPT ![p][r] = TRUE]
                    ELSE OLD_broadcastRecord
               IN
               LET tmp1_OLD_buffer == OLD_buffer IN
               LET tmp1_OLD_dag == OLD_dag IN
               LET tmp1_OLD_round == [OLD_round EXCEPT ![p] = OLD_round[p]+1] IN
               
               (* Third step : deliver the vertex and adds it to the local buffer *)
               LET tmp2_OLD_blocksToPropose == tmp1_OLD_blocksToPropose IN
               LET tmp2_OLD_broadcastNetwork == [tmp1_OLD_broadcastNetwork EXCEPT 
                            ![p] = tmp1_OLD_broadcastNetwork[p] \ 
                            {[sender |-> p, inRound |-> r, vertex |-> v]}] IN
               LET tmp2_OLD_broadcastRecord == tmp1_OLD_broadcastRecord IN
               LET tmp2_OLD_buffer == [tmp1_OLD_buffer EXCEPT ![p] = tmp1_OLD_buffer[p] \cup {v}] IN
               LET tmp2_OLD_dag == tmp1_OLD_dag IN
               LET tmp2_OLD_round == tmp1_OLD_round IN
               
               (* Fourth step : process the vertex *)
               /\ OLD_blocksToPropose' = tmp2_OLD_blocksToPropose
               /\ OLD_broadcastNetwork' = tmp2_OLD_broadcastNetwork
               /\ OLD_broadcastRecord' = tmp2_OLD_broadcastRecord
               /\ OLD_buffer' = tmp2_OLD_buffer
               /\ OLD_dag' = [tmp2_OLD_dag EXCEPT ![p][v.round][v.source] = v]
               /\ OLD_round' = tmp2_OLD_round
         ELSE \E p \in ProcessorSet, q \in ProcessorSet :
            /\  AddVertexTn(p, [round |-> ProcessState[p][q]+1, source |-> q])
            /\  (* First step : deliver the vertex and adds it to the buffer *)
                LET r == ProcessState[p][q]+1 IN
                LET flagedv == CHOOSE y \in OLD_broadcastNetwork : 
                    y.sender = q /\ y.inRound = r
                IN
                LET v == flagedv.vertex IN
                LET tmp_OLD_blocksToPropose == OLD_blocksToPropose IN
                LET tmp_OLD_broadcastNetwork == [OLD_broadcastNetwork EXCEPT 
                                ![p] = OLD_broadcastNetwork[p] \ 
                                {[sender |-> q, inRound |-> r, vertex |-> v]}] IN
                LET tmp_OLD_broadcastRecord == OLD_broadcastRecord IN
                LET tmp_OLD_buffer == [OLD_buffer EXCEPT ![p] = OLD_buffer[p] \cup {v}] IN
                LET tmp_OLD_dag == OLD_dag IN
                LET tmp_OLD_round == OLD_round IN
                
                (* Second step : process the vertex *)
                /\ OLD_blocksToPropose' = tmp_OLD_blocksToPropose
                /\ OLD_broadcastNetwork' = tmp_OLD_broadcastNetwork
                /\ OLD_broadcastRecord' = tmp_OLD_broadcastRecord
                /\ OLD_buffer' = tmp_OLD_buffer
                /\ OLD_dag' = [tmp_OLD_dag EXCEPT ![p][v.round][v.source] = v]
                /\ OLD_round' = tmp_OLD_round

Inv ==
    \A p \in ProcessorSet :
        ProcessState[p][p] <= 10

Temporal ==
    [](\A p \in ProcessorSet : ProcessState[p][p] >= ProcessState[p+1][p+1])
        => []Inv
        
Spec == Init /\ [][Next]_<<dag, ProcessState, OLD_blocksToPropose,
                            OLD_broadcastNetwork, OLD_broadcastRecord,
                            OLD_buffer, OLD_dag, OLD_round>>

=============================================================================
\* Modification History
\* Last modified Tue Mar 05 13:59:28 AEDT 2024 by emmanuel
\* Created Wed Feb 28 08:18:24 AEDT 2024 by emmanuel
