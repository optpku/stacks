module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Termwise
import StacksCheckRecall

/-!
# Bounded complexes with perfect terms

Lemma 15.75.6 states that a bounded cochain complex of perfect modules is perfect in the derived
category.  The reusable statement is owned by ReasLib.

@stack 066T
-/

@[expose] public section

-- Lemma 15.75.6 (066T): a bounded complex of perfect modules is a perfect complex.
@[stacks 066T "Lemma 15.75.6"]
#check @CochainComplex.Bounded.isPerfect
