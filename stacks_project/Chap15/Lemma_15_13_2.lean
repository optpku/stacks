module

public import ReasLib.RingTheory.Henselian.FiniteEtale
import StacksCheckRecall

/-!
# Finite etale algebras over a henselian pair

@stack 09ZL

Lemma 15.13.2: if `(A, I)` is a henselian pair, reduction modulo `I` induces an equivalence
between finite etale `A`-algebras and finite etale `A ⧸ I`-algebras. The source functor is the
canonical finite-etale base-change functor `CommAlgCat.FiniteEtale.reduction I`.
-/

@[expose] public section

open CategoryTheory

@[stacks 09ZL "finite-etale category"]
#check @CommAlgCat.FiniteEtale

@[stacks 09ZL "reduction modulo the henselian ideal"]
#check @CommAlgCat.FiniteEtale.reduction

@[stacks 09ZL "Lemma 15.13.2"]
#check @CommAlgCat.FiniteEtale.reduction_isEquivalence

#print axioms CommAlgCat.FiniteEtale.reduction
#print axioms CommAlgCat.FiniteEtale.reduction_isEquivalence
