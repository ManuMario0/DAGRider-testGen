(* The DAG-Rider Specification defines a state transition system  for the  *)
(* DAG-Rider protocol, and its safety properties. The article for the      *)
(* protocol can be found here:   https://arxiv.org/abs/2102.08325          *)

------------------------ MODULE DAGRiderSpecification -----------------------

EXTENDS FiniteSets,
        Integers,
        Sequences,
        Apalache

-----------------------------------------------------------------------------

(*---------------------------------ALIASES---------------------------------*)

(*
    @typeAlias: vertex = {
        round : Int,
        source : Int,
        block : BLOCK,
        strongedges : Set(Int),
        weakedges : Set(Int)
    };
*)
DAGRiderSpecification_typedefs == TRUE


(*--------------------------------CONSTANTS--------------------------------*)

(* NumProcessors is the number of participating processes in the protocol. *)
(* We assume this is non zero. We number processes 1 to NumProcessors,     *)
(* and define ProcessorSet as the set of participating processes.          *) 
(* We define maximum allowed process failures (NumFaultyProcessors) as the *)
(* greatest integer less than one third of the total number of processes.  *)

CONSTANT
    \* @type: Int;
    NumProcessors

ASSUME NumProcessorAsm == 
   NumProcessors \in Nat\{0}

NumFaultyProcessors == 
   (NumProcessors-1) \div 3

ProcessorSet == 
   1..NumProcessors

(* For type consistency, I changed the "History" labbel to the value -1.   *)
(* So that it is easier to follow, I added the function History.           *)

History == -1

ASSUME ProcSetAsm == 
   History \notin ProcessorSet
   
(* I introduce this interval so that Apalache STOP COMPLAINS ABOUT NON     *)
(* CONSTANT BOUNDS !!!!!                                                   *)

BigInterval == -1..1
BuildSetFromBounds(lowerBound, upperBound) ==
    {y \in BigInterval : y >= lowerBound /\ y < upperBound}

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
    \* @type: Set(BLOCK);
    BlockSet

-----------------------------------------------------------------------------

(* ChooseLeader(_) is function that maps WaveSet to ProcessorSet.          *)

CONSTANT
    \* @type: Int => Int;
    ChooseLeader(_)

-----------------------------------------------------------------------------

(* NilVertex(p, r) is a vertex which represents the non-existence of a mes-*)
(* sage and whose block is Nil. To make the DAG more expressive we assume  *)
(* that DAG of every process has a vertex in every round created by every  *)
(* process. In practice, a process q might not have added a vertex created *)
(* by process p in round r in this case we assume that it has a Nil-       *)
(* Vertex(p, r).  We define NilVertexSet as the set of all nil vertices.   *)

(* I changed the "Nil" block name to "NIL_OF_BLOCK" for type compatibility *)

\* @type: (Int, Int) => $vertex;
NilVertex(p, r) ==
   [round |-> r,
    source |-> p,
    block |-> "NIL_OF_BLOCK",
    strongedges |-> {},
    weakedges |-> {}]

NilVertexSet == 
   {NilVertex(p, r) : p \in ProcessorSet, r \in RoundSet}

(* I am not bidding direclty the Append function for type annotation       *)
(* issues. This is an issue in apalache : if you use polymorphic func-     *)
(* -tions, it has sometimes trouble typing them and keeps them as          *)
(* polymorphic in our case. The reason for that is it cannot infer the     *)
(* type it has to give to Apppend in ApaFoldSet from the other parameters  *)
(* yet. Therefore we use a cutom binding for correct typin                 *)

\* @type: (Seq($vertex), $vertex) => Seq($vertex);
CustomAppend(s, e) ==
    Append(s, e)

(* I am using sequences intead of sets, see next comments                  *)

\* @type: Seq($vertex);
NilVertexSeq ==
    ApaFoldSet(CustomAppend, <<>>, NilVertexSet)

-----------------------------------------------------------------------------

(* Since we have bounded the number waves, there is a finite set of verti- *)
(* ces (VertexSet), which can be created by the participating processes.   *)
(* To define VertexSet, we first define ZeroRoundVertexSet (i.e., a set of *)
(* dummy vertices in round 0 of the DAG). Then, we define set              *)
(* UntilRoundVertex(r), which is set of vertices till round r. It is       *)
(* important to note that a vertex as defined in DAG-rider is not a vertex *)
(* but a rooted DAG (aka. downset). The downset stores the entire causal   *)
(* history of the node.                                                    *) 

(* Update : because we wanted to use Apalache for some trace generation,   *)
(* we changed the structure to not referenced the vertices directly but    *)
(* through an ID. Another thing is a limitation of Apalache, forcing us    *)
(* not to use recursive functions as well, that is why the structure of    *)
(* the spec is a lot impacted.                                             *)

\* @type: Int => $vertex;
ZeroRoundVertexID(p) == 
   [round |-> 0, 
    source |-> p,
    block |-> "EMPTY_OF_BLOCK",
    strongedges |-> {},
    weakedges |-> {}]
    
ZeroRoundVertexSequenceAux(s, p) ==
    Append(s, ZeroRoundVertexID(p))
    
Constructor(n) == n

ZeroRoundVertexSeq ==
    ApaFoldSeqLeft(
                    ZeroRoundVertexSequenceAux,
                    NilVertexSeq,
                    MkSeq(NumProcessors, Constructor)
                  )

\* @type: (Seq($vertex), Int) => Seq($vertex);
UntilRoundVertexID(s, r) ==
    ApaFoldSet(
                    CustomAppend,
                    s,
                    [ 
                        round : {r},
                        source : ProcessorSet,
                        block : BlockSet,
                    (* I might change those to DOMAIN s for clairity later on *)
                    (* Or even better : avoid the NilVertex part !            *)
                        strongedges : SUBSET(BuildSetFromBounds(0, Len(s))),
                        weakedges : SUBSET(BuildSetFromBounds(0, Len(s)))
                    ]
    )

VertexSeq ==
    ApaFoldSeqLeft(
                    UntilRoundVertexID,
                    ZeroRoundVertexSeq,
                    MkSeq(4*NumWaves, Constructor)
                  )

NumVertex == Len(VertexSeq)
VertexIndices == BuildSetFromBounds(Len(NilVertexSeq), NumVertex) (*Len(NilVertexSeq)..NumVertex-1*)

ZeroRoundVertexIndices == Len(NilVertexSeq)..Len(ZeroRoundVertexSeq)-1
NilVertexIndices == BuildSetFromBounds(0, Len(NilVertexSeq)) (* 0..Len(NilVertexSeq)-1 *)

GetVertexFromID(id) == VertexSeq[id]
GetIDFromVertex(v) == Guess({id \in DOMAIN VertexSeq : GetVertexFromID(id) = v})

-----------------------------------------------------------------------------

(* When a vertex is broadcasted, the broadcast tags the vertex with its    *)
(* sender and the round in which it was sent. TaggedVertexSet is the set   *)
(* of all such tagged vertices.                                            *)

TaggedVertexSetID ==
   [sender : ProcessorSet, inRound : RoundSet, vertex : VertexIndices]

-----------------------------------------------------------------------------

(*--------------------------STATE-VARIABLES--------------------------------*)

(* For every process p, blocksToPropose stores a sequence of blocks that   *)
(* are proposed but not yet initialized to order (blocks whose vertex is   *)
(* not yet created by the process).                                        *)

VARIABLE
    \* @type: Int -> Seq(BLOCK);
    blocksToPropose

BlocksToProposeType == 
   blocksToPropose \in [ProcessorSet -> Seq(BlockSet)]

(* For reasons that I still don't understands, for this specific instance, *)
(* I cannot use p \in ProcessorSet. If I don't, Apalache complains         *)
InitBlocksToPropose ==  
   blocksToPropose = [p \in BuildSetFromBounds(1, NumProcessors+1) |-> <<>> ]

-----------------------------------------------------------------------------

(* For every process p, broadcastNetwork stores set of TaggedVertices that *)
(* are broadcasted but not yet received by p. Additionally it also stores  *)
(* history of all the TaggedVertices ever broadcasted on the network.      *)

(* PLEASE CHECK LATER BECAUSE MOSTLIKELY WRONG *)
(* Just checked : it is indeed wrong hehe *)

VARIABLE
    \* @type: Int -> Set({sender: Int, inRound: Int, vertex: $vertex});
    broadcastNetwork

(* I have to fix this later on cause rn I'm still using explicit $vertex   *)
(* in some spot in the spec and I cannot use the SUBSET operator on it     *)
(* directly.                                                               *)
    
(*
BroadcastNetworkType == 
   broadcastNetwork \in [ProcessorSet \cup 
                         {-1} -> SUBSET(VertexSeq)]
*)

InitBroadcastNetwork == 
   broadcastNetwork = [p \in BuildSetFromBounds(1, NumProcessors+1) \cup {History} |-> {}]

-----------------------------------------------------------------------------

(* For every process p and round r, broadcastRecord stores whether or not  *)
(* process p broadcasted a vertex in round r.                              *)

VARIABLE
    \* @type: Int -> Int -> Bool;
    broadcastRecord

BroadcastRecordType == 
   broadcastRecord \in [ProcessorSet -> [RoundSet -> BOOLEAN]]

InitBroadcastRecord == 
   broadcastRecord = [p \in ProcessorSet |-> 
      [ r \in RoundSet |-> IF r = 0 THEN TRUE ELSE FALSE ]]

-----------------------------------------------------------------------------

(* For every process p, buffer stores set of vertices received by p via    *)
(* the broadcast.                                                          *)

VARIABLE
    \* @type: Int -> Set($vertex);
    buffer

BufferType == 
   buffer \in [ProcessorSet -> SUBSET({VertexSeq[i]: i \in VertexIndices})]

InitBuffer ==
   buffer = [p \in BuildSetFromBounds(1, NumProcessors+1) |-> {}]

-----------------------------------------------------------------------------

(* For every process p, round r, process q, dag stores vertex in the DAG   *)
(* of process p created by process q in round r, if such a vertex does not *)
(* exists in the DAG then it stores NilVertex(q, r).                       *)

VARIABLE
    \* @type: Int -> Int -> Int -> Int;
    dag

DagType == 
   dag \in [ProcessorSet -> 
      [RoundSet  -> [ProcessorSet -> VertexIndices \cup NilVertexIndices]]]

(* I'm currently using the Guess operator of apalche but I want to cahnge  *)
(* The only thing is, I currently don't know how to get rid of it, maybe   *)
(* LET ??                                                                  *)

InitDag == 
   dag = [p \in ProcessorSet |-> 
      [r \in RoundSet  |-> [q \in ProcessorSet |-> 
         IF r = 0 
         THEN Guess({y \in BigInterval :
                        y >= Len(NilVertexSeq)
                        /\ y < Len(ZeroRoundVertexSeq)
                        /\ VertexSeq[y].source = q})
         ELSE Guess({y \in BigInterval : y < Len(NilVertexSeq) /\
                        VertexSeq[y].source = q /\ VertexSeq[y].round = r})
      ]]]

-----------------------------------------------------------------------------

(* For every process p, round stores the round of DAG construction for     *)
(* process p.                                                              *) 

VARIABLE
    \* @type: Int -> Int;
    round

RoundType == 
   round \in [ProcessorSet -> RoundSet]

InitRound == 
   round = [p \in ProcessorSet |-> 0]

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
        NumProcessors <- NumProcessors,
        commitWithRef <- commitWithRef,
        decidedWave <- decidedWave,
        leaderReachablity <- leaderReachablity,
        leaderSeq <- leaderSeq

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

(* I had to design a pathfinding algorithm a little bit smart here because *)
(* of the absence of real recurivity in Apalache. What I did is compute    *)
(* from the bottom-up the vertex that can reach the target, up to the      *)
(* total rounds in the run. This assure us we compute all of the states    *)
(* that reach the target. The final step is to check if our starting point *)
(* is in the set.                                                          *)

\* @type: (Set(Int), Int) => Set(Int);
PathAux(set, ignore) ==
    { x \in VertexIndices :
        (set \intersect
            (GetVertexFromID(x).weakedges \cup GetVertexFromID(x).strongedges)
        ) # {}
        \/ x \in set }

\* @type: (Int, Int) => Bool;
Path(u, v) ==
    u \in ApaFoldSet(PathAux, {v}, RoundSet)

\* @type: (Set(Int), Int) => Set(Int);
StrongPathAux(set, ignore) ==
    { x \in VertexIndices :
        (set \intersect GetVertexFromID(x).strongedges) # {}
        \/ x \in set }

StrongPath(u, v) ==
    u \in ApaFoldSet(StrongPathAux, {v}, RoundSet)

InAddedVertex(p, r) == 
   { v \in VertexIndices :
        GetVertexFromID(v).round = r
        /\ dag[p][r][GetVertexFromID(v).source] = v }

\* @type: (Seq(Set(Int)), Int) => Seq(Set(Int));
UntilAddedVertexAux(pair, r) ==
    <<pair[0], InAddedVertex(Guess(pair[0]), r) \cup pair[1]>>

(* For type consistency I put p in a set even though this not the most    *)
(* natural thing to do.                                                   *)
(*                                                                        *)
(* NOTE : I could have use FoldSet since the order is not important,      *)
(* might be usefull for efficiency                                        *)

UntilAddedVertex(p, r) ==
    ApaFoldSeqLeft( UntilAddedVertexAux, <<{p},
                    InAddedVertex(p, 0)>>,
                    MkSeq(r, Constructor)
                  )[1]

NoPathVertices(p, r) == {v \in UntilAddedVertex(p, r) : 
                         (\A w \in InAddedVertex(p, r) : ~Path(w,v))}                         

\* @type: (Int, Int) => Int;
WaveLeader(p, w) == dag[p][4*w-3][ChooseLeader(w)]

-----------------------------------------------------------------------------

(* Transition ProposeTn(p, b) encodes process p proposing block b.         *)

\* @type: (Int, BLOCK) => Bool;
ProposeTn(p, b) == 
   /\ blocksToPropose' = [blocksToPropose EXCEPT 
         ![p] = Append(blocksToPropose[p], b)]
   /\ UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<broadcastNetwork, broadcastRecord, buffer, dag, round>>

-----------------------------------------------------------------------------

(* Transition NextRoundTn(p) encodes process p moving to the next round of *)
(* DAG construction.  Upon completion of the current round process p moves *)
(* to the next round by creating (CreateVertex) and broadcasting (Broadcast*)
(* a new vertex. Additionally, when next round leads to a new wave it tries*)
(* to decide the current wave (ReadyWave), if decide condition is satisfied*)
(* it takes UpdateDecidedWaveTn in LeaderConsensus.                        *)

\* @type: (Int, Int) => $vertex;
CreateVertex(p, r) == 
   [round |-> r, 
    source |-> p, 
    block |-> Head(blocksToPropose[p]), 
    strongedges |-> InAddedVertex(p, r-1),
    weakedges |-> NoPathVertices(p, r-1)]

\* @type: (Int, Int, $vertex) => Bool;
Broadcast(p, r, v) == 
   IF broadcastRecord[p][r] = FALSE
   THEN /\ broadcastRecord' = [broadcastRecord EXCEPT ![p][r] = TRUE]
        /\ broadcastNetwork' = [q \in ProcessorSet \cup {History} 
              |-> broadcastNetwork[q] \cup 
                  {[sender |-> p, inRound |-> r, vertex |-> v]}]
   ELSE UNCHANGED <<broadcastNetwork, broadcastRecord>>

\* @type: (Int, Int) => Bool;
ReadyWave(p, w) == 
   IF ( /\ dag[p][4*w-3][WaveLeader(p, w)] \in VertexIndices
        /\ \E Q \in SUBSET(InAddedVertex(p, 4*w)):
              /\ Cardinality(Q) > 2*NumFaultyProcessors 
              /\ \A u \in Q : StrongPath(u, WaveLeader(p, w)) )
   THEN LeaderConsensus!UpdateDecidedWaveTn(p, w)
   ELSE UNCHANGED LeaderConsensus!vars

\* @type: Int => Bool;
NextRoundTn(p) ==  
   /\ round[p]+1 \in RoundSet
   /\ Cardinality(InAddedVertex(p, round[p])) > 2*NumFaultyProcessors
   /\ blocksToPropose[p] # <<>>
   /\ Broadcast(p, round[p]+1, CreateVertex(p, round[p]+1))
   /\ round' = [round EXCEPT ![p] = round[p]+1]
   /\ blocksToPropose' = [blocksToPropose EXCEPT 
         ![p] = Tail(blocksToPropose[p])]
   /\ IF round[p]>0 /\ (round[p] % 4) = 0 
      THEN ReadyWave(p, (round[p] \div 4)) 
      ELSE UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<buffer, dag>>

-----------------------------------------------------------------------------

(* Transition ReceiveVertexTn(p, q, r, v) encodes process p receiving      *)
(* vertex v created in round r by process q.                               *)

\* @type: (Int, Int, Int, $vertex) => Bool;
ReceiveVertexTn(p, q, r, v) == 
   /\ [sender |-> q, inRound |-> r, vertex |-> v] \in broadcastNetwork[p]
   /\ v.source = q
   /\ v.round = r
   /\ Cardinality(v.strongedges) > 2*NumFaultyProcessors
   /\ buffer' = [buffer EXCEPT ![p] = buffer[p] \cup {v}]
   /\ broadcastNetwork' = [broadcastNetwork EXCEPT 
         ![p] = broadcastNetwork[p] \ 
             {[sender |-> q, inRound |-> r, vertex |-> v]}]
   /\ UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<blocksToPropose, broadcastRecord, dag, round>>

-----------------------------------------------------------------------------

(* Transition AddVertexTn(p, v) encodes process p adding  vertex v from the*)
(* buffer to the DAG. Additionally, if v is a leader vertex of some wave   *)
(* then UpdateWaveTn is performed on LeaderConsensus. For this update, we  *)
(* compute set of waves whose leader vertex in p, is in strong causal      *)
(* history of v (ReachableWaveLeaders).                                    *)

\* @type: (Int, Int) => Set(Int);
ReachableWaveLeaders(p, v) == 
   {w \in WaveSet : StrongPath(v, WaveLeader(p, w))}

\* @type: (Int, $vertex) => Bool;
AddVertexTn(p, v) == 
   /\ v \in buffer[p]
   /\ v.round <= round[p]
   /\ GetVertexFromID(dag[p][v.round][v.source]) = NilVertex(v.source, v.round)
   /\ (v.strongedges \cup v.weakedges) \in SUBSET(InAddedVertex(p, v.round -1))
   /\ dag'= [dag EXCEPT ![p][v.round][v.source] = GetIDFromVertex(v)]
   /\ IF v.round % 4 = 1 /\ v.source = ChooseLeader((v.round \div 4)+1)
      THEN LeaderConsensus!UpdateWaveTn(
            p,
            (v.round \div 4)+1,
            ReachableWaveLeaders(p, GetIDFromVertex(v))
           ) 
      ELSE UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<blocksToPropose, broadcastNetwork, 
                  broadcastRecord, buffer, round>>

-----------------------------------------------------------------------------

(*--------------------------TRANSITION-SYSTEM------------------------------*)

(* To complete the transition system specification, we define Init, Next,  *)
(* vars, Spec. Typical TLA+ macro names for the initial state, possible    *)
(* actions leading to the next state, the variables, and the system spec-  *)
(* ification, respectively.                                                *)
(*
StateType ==
   /\ BlocksToProposeType
   /\ BroadcastNetworkType
   /\ BroadcastRecordType
   /\ BufferType
   /\ DagType
   /\ RoundType
*)

Init == 
   /\ InitBlocksToPropose
   /\ InitBroadcastNetwork
   /\ InitBroadcastRecord
   /\ InitBuffer
   /\ InitDag
   /\ InitRound
   /\ LeaderConsensus!Init

vars == <<blocksToPropose, broadcastNetwork, broadcastRecord, buffer, 
          commitWithRef, dag, decidedWave, leaderReachablity, leaderSeq, 
          round>>

Next == UNCHANGED vars (*
   \E p \in ProcessorSet, r \in RoundSet, v \in VertexIndices, b \in BlockSet: 
      \E q \in ProcessorSet\{p}:
         \/ ProposeTn(p, b)
         \/ NextRoundTn(p)
         \/ ReceiveVertexTn(p, q, r, GetVertexFromID(v))
         \/ AddVertexTn(p, GetVertexFromID(v))*)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(*--------------------------SAFETY-INVARIANTS------------------------------*)

(* DagConsistency states that if vertex created by a process o in a round r*)
(* is added to the DAG of process p and q then they are the same vertices. *)
(* Note that a vertex stores its entire causal history, thus their causal  *)
(* histories are same.                                                     *)

DagConsistency == 
   \A p, q \in ProcessorSet, r \in RoundSet, o \in ProcessorSet: 
     (/\ r # 0 
      /\ dag[p][r][o] \in VertexIndices 
      /\ dag[q][r][o] \in VertexIndices ) => dag[p][r][o] = dag[q][r][o]

-----------------------------------------------------------------------------

(* LeaderConsistency and LeaderMonotonicity are same as defined in Leader- *)
(* ConsensusSpecification.                                                 *)

LeaderConsistency == 
   \A p, q \in ProcessorSet: 
      decidedWave[p] <= decidedWave[q] => 
         LeaderConsensus!IsPrefix(leaderSeq[p].current, leaderSeq[q].current)

LeaderMonotonicity == 
   \A p \in ProcessorSet: 
      LeaderConsensus!IsPrefix(leaderSeq[p].last, leaderSeq[p].current)

-----------------------------------------------------------------------------

Safety == Spec => [](DagConsistency /\ LeaderConsistency /\ LeaderMonotonicity)

=============================================================================
