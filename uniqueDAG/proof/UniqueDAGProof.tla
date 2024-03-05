--------------------------- MODULE UniqueDAGProof ---------------------------

EXTENDS UniqueDAGSpec,
        FiniteSets,
        Integers,
        Sequences,
        TLAPS,
        TLC

Equivalence ==
    \A p \in ProcessorSet, q \in ProcessorSet, r \in RoundSet\{0} :
        IF ProcessState[p][q] < r
        THEN OLD_dag[p][r][q].block = "Nil"
        ELSE
            /\ dag[q][r].block = OLD_dag[p][r][q].block
            /\ TRUE

LEMMA CorrectEquivalence == Spec => []Equivalence
OBVIOUS

=============================================================================
\* Modification History
\* Last modified Tue Mar 05 14:33:40 AEDT 2024 by emmanuel
\* Created Tue Mar 05 13:26:01 AEDT 2024 by emmanuel
