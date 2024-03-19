------------------------------ MODULE DAGRider ------------------------------

EXTENDS Integers, FiniteSets

CONSTANT
    NumProcess,
    NumWaves,
    ChooseLeader(_)
 
ProcessSet ==
    1..NumProcess
    
ExternProcessSet ==
    2..NumProcess
    
NumRound ==
    4*NumWaves
    
RoundSet ==
    0..NumRound
    
f ==
    (NumProcess - 1) \div 3
    
\* @type: {block : Int, strongedges : Set({source : Int, round : Int}), weakedges : Set({source : Int, round : Int}), reachableleaders : Set(Int)};
NoneVertex ==
    [
        block |-> 0,
        strongedges |-> {},
        weakedges |-> {},
        reachableleaders |-> {}
    ]

VARIABLES
    \* @type: Int;
    nextBlock,
    \* @type: Int -> Int -> $vertex;
    dag,
    \* @type: Seq(Int);
    orderedBlock,
    \* @type: Set($vertex);
    buffer,
    \* @type: Int -> Int -> Bool;
    isDelivered,
    \* @type: $vertex;
    lastVertexDelivery,
    \* @type: $vertex;
    lastVertexBroadcast,
    \* @type: Int -> Int;
    round,
    \* @type: Set(Int)
    weakHead

InitNextBlock ==
    nextBlock = 1

InitDag ==
    dag = [p \in ProcessSet |-> [r \in RoundSet |-> NoneVertex]]

InitOrderedBlock ==
    orderedBlock = <<>>
    
InitBuffer ==
    buffer = {}

InitIsDelivered ==
    isDelivered = [p \in ExternProcessSet |-> [r \in RoundSet |-> FALSE]]
    
InitLastVertexDelivery ==
    lastVertexDelivery = NoneVertex
    
InitLastVertexBroadcast ==
    lastVertexBroadcast = NoneVertex
    
InitRound ==
    round = [p \in ProcessSet |-> 0]
    
InitWeakHead ==
    weakHead = ProcessSet

(*
    Receive a vertex from the network
    As we are running in an emulated environment, we have
    to be able to handle every possible vertex input and deal with it.
    
    Whatever the form of the vertex that we receive, we will not be able to send a
    vertex on this pair (p, r) after that anymore. Moreover, if the vertex is well 
    formed, then it will be added to the buffer of the process
 *)
T_ReceiveVertex(p, r, v) ==
    /\ v.block = nextBlock
    /\ nextBlock' = nextBlock + 1
    /\ isDelivered[p][r] = FALSE
    /\ isDelivered' = [isDelivered EXCEPT ![p][r] = TRUE]
    /\ lastVertexDelivery' = v
    /\ IF   /\ v.source = p
            /\ v.round = r
            /\ Cardinality(v.strongedges) > 2*f
            /\ \A tmp_v \in v.strongedges : tmp_v.round = r-1
            /\ \A tmp_v \in v.weakedges : tmp_v.round < r-1
            /\ \E tmp_v \in v.strongedges : tmp_v.source = v.p /\ tmp_v.round = v.round-1
        THEN
            buffer' = buffer \cup {v}
        ELSE
            UNCHANGED <<buffer>>
    /\ UNCHANGED <<dag, orderedBlock, round, weakHead, lastVertexBroadcast>>

(*
    Move all vertex that are movable from the buffer to the DAG
    
    There are two reasons why we want to unload them all at once :
    1. In the paper, the vertex in buffer are actually processed like that
    (assuming some concurency restricitions on the execution of their code)
    -> Fair enough this point does not holds because it would need to find
    a fixpoint which I don't want so we're gonna keep it this way
    espacially cause we technicaly can come back to it by sayin' that
    if a vertex can still be added after then it'll be by the priority
    given to this function. That is, if a vertex is missed, then it'll be added
    next round in the worst case and let the model-checker find the fixpoint for us
    
    2. It is easier for the model checker becuase it reduces the size of
    the execution graph to process. This property is particularly interesting
    in the  context of testing because it reduces by a lot the number of partial order
    reduction to simplify
*)
T_MoveVertexToDAG ==
        (*
            This is the list of vertex to add to the DAG
            We add every vertex which has a lower round than ours
            and have all of their dependences in the DAG
        *)
    LET addedVertex == {v \in buffer : 
        /\ \A tmp_v \in v.strongedges \cup v.weakedges : dag[tmp_v.source][tmp_v.round].block # 0
        /\ v.round <= round[1]
    } IN
        (*
            We remove those vertex from the buffer ...
        *)
    /\ buffer' = buffer \ addedVertex
        (*
            ... to add them to the DAG
        *)
    /\ dag' = [
        p \in ProcessSet |-> [
            r \in RoundSet |->
                IF \E v \in addedVertex : p = v.source /\ r = v.round
                THEN
                    LET v == CHOOSE v \in addedVertex : p = v.source /\ r = v.round IN
                    [
                        block |-> v.block,
                        strongedges |-> v.strongedges,
                        weakedges |-> v.weakedges,
                        reachableleaders |->
                            UNION { dag[q][r-1].reachableleaders :
                                q \in v.strongedges }
                            \union (
                                IF (r % 4) = 1 /\ ChooseLeader((r+3) \div 4) = p
                                THEN { (r+3) \div 4 }
                                ELSE {}
                            )
                    ]
                ELSE
                    dag[p][r]
        ]
     ]
        (*
            We update the weakhead such that we always keep in the set
            the verteces that are not recheable from our last added vertex
            or from a vertex in the set with a higher round in our local DAG
            
            For that we do two things :
            1. Remove all the vertex from it such that there is an edge from
            one of the vertex we added to the DAG
            2. Then we add all the new verteces because there is know incomming
            edge by the dependency property
        *)
    /\ weakHead' = (weakHead \ {x.source : x \in UNION {v.strongedges \cup v.weakedges : v \in addedVertex}})
        \cup {v.source : v \in addedVertex}
        (*
            We update the round of the process of the added vertex
            Remember that we deviate from the acutal protocol by enforcing
            that a vertex must be linked to the one in the round before
        *)
    /\ round' = [
        p \in ProcessSet |->
            IF \E v \in addedVertex : v.source = p
            THEN (CHOOSE v \in addedVertex : v.source = p).round
            ELSE round[p]
       ]
    /\ UNCHANGED <<nextBlock, orderedBlock, isDelivered, lastVertexDelivery, lastVertexBroadcast>>

(*
    Here we add a vertex ourself.
    We change the algorithm such that the vertex
    is directly added to the graph without waiting
*)
T_AddVertex ==
    (*
        Vertex constructed by the algorithm
    *)
    LET v == [
        block |-> nextBlock,
        strongedges |-> [
            round: {round[1]},
            source: {p \in ProcessSet : dag[p][round[1]].block # 0}
        ],
        weakedges |-> {
            [
                round |-> round[v.source],
                source |-> v
            ] : v \in weakHead
        },
        reachableleaders |->
            UNION { dag[q][round[1]].reachableleaders :
                                q \in [
                                    round: {round[1]},
                                    source: {p \in ProcessSet : dag[p][round[1]].block # 0}
                            ] }
                            \union (
                                IF ((round[1]+1) % 4) = 1 /\ ChooseLeader((round[1]+4) \div 4) = 1
                                THEN { (round[1]+4) \div 4 }
                                ELSE {}
                            )
    ] IN
    /\ Cardinality({p \in ProcessSet : dag[p][round[1]].block # 0}) > 2*f
    /\ dag' = [
        dag EXCEPT ![1][round[1]] = v
       ]
    /\ round' = [
        round EXCEPT ![1] = round[1]+1
       ]
    /\ weakHead' = {1}
    /\ lastVertexBroadcast' = v
    /\ nextBlock' = nextBlock + 1
    /\ UNCHANGED <<orderedBlock, isDelivered, lastVertexDelivery>>

Init ==
    /\ InitNextBlock
    /\ InitDag
    /\ InitOrderedBlock
    /\ InitBuffer
    /\ InitIsDelivered
    /\ InitLastVertexDelivery
    /\ InitLastVertexBroadcast
    /\ InitRound
    /\ InitWeakHead

Next ==
    IF Cardinality({v \in buffer : 
        /\ \A tmp_v \in v.strongedges \cup v.weakedges : dag[tmp_v.source][tmp_v.round].block # 0
        /\ v.round <= round[1]
        }) > 0
    THEN T_MoveVertexToDAG
    ELSE IF Cardinality({p \in ProcessSet : dag[p][round[1]].block # 0}) > 2*f
    THEN T_AddVertex
    ELSE \E p \in ExternProcessSet, r \in RoundSet, v \in
        [
            block : { nextBlock },
            source : ProcessSet,
            round : RoundSet,
            weakedges : SUBSET([source : ProcessSet, round : RoundSet]),
            strongedges : SUBSET([source : ProcessSet, round : RoundSet])
        ] : T_ReceiveVertex(p, r, v)

=============================================================================
\* Modification History
\* Last modified Tue Mar 19 17:09:34 AEDT 2024 by emmanuel
\* Created Wed Mar 06 11:04:57 AEDT 2024 by emmanuel
