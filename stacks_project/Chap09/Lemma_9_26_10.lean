module

public import Mathlib.RingTheory.Algebraic.Integral
import StacksCheckRecall

@[expose] public section

/-!
Lemma 9.26.10 (Tag 0G1M) is the finite-dimensional specialization of the canonical rank
comparison for rational function fields after scalar extension.
-/

@[stacks 0G1M]
#check Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial
