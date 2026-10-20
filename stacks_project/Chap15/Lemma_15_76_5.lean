module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.QuotientLifting
import StacksCheckRecall

/-!
# Lemma 15.76.5 (0BCB)

@stack 0BCB
-/

@[expose] public section

/- Lemma 15.76.5: bounded-above finite-stably-free representatives lift across a Jacobson
quotient, preserving termwise freeness. -/
@[stacks 0BCB "Lemma 15.76.5"]
#check @CategoryTheory.DerivedCategory.QuotientLifting.exists_finiteStablyFree
