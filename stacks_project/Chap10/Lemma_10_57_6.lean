/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GradedAlgebra.Irrelevant.PrimeAvoidance
import StacksCheckRecall

@[expose] public section

/-!
# Finite homogeneous-prime avoidance

@stack 00JS

The finite prime-avoidance theorem is owned by `HomogeneousIdeal`; this entry
records its source contract.
-/

/- Lemma 10.57.6: a homogeneous ideal contained in the irrelevant ideal and not contained in
any of finitely many homogeneous prime ideals contains a positive-degree homogeneous element
avoiding all of them. -/
@[stacks 00JS]
#check @HomogeneousIdeal.exists_posDegree_mem_avoid_primes

end
