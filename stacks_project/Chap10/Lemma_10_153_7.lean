module

public import ReasLib.RingTheory.Henselian.FiniteEtale
import StacksCheckRecall

@[expose] public section

/-!
# Finite etale special fibers

@stack 04GK

Lemma 10.153.7 is the closed-point specialization of the neutral
henselian-pair equivalence
`CommAlgCat.FiniteEtale.reduction_isEquivalence`.  The maximal-ideal case is
obtained by typeclass specialization and needs no chapter wrapper.
-/

@[stacks 04GK "finite etale owner"]
#check @CommAlgCat.FiniteEtale
@[stacks 04GK "base change owner"]
#check @CommAlgCat.FiniteEtale.baseChange
@[stacks 04GK "reduction owner"]
#check @CommAlgCat.FiniteEtale.reduction
@[stacks 04GK "canonical equivalence"]
#check @CommAlgCat.FiniteEtale.reduction_isEquivalence

#print axioms CommAlgCat.FiniteEtale.reduction_isEquivalence
