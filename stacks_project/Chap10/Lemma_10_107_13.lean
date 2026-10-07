module

public import ReasLib.RingTheory.Algebra.IsEpi
import StacksCheckRecall

/-!
# Cardinality of an epic algebra

@stack 04W0

Lemma 10.107.13 is a direct recall of the cardinality bound owned by
`Algebra.IsEpi`.
-/

@[expose] public section

-- Lemma 10.107.13 (Tag 04W0): the target of an epimorphism of commutative rings
-- has cardinality at most that of its source.
@[stacks 04W0] #check @Algebra.IsEpi.cardinalMk_le
