/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
import StacksCheckRecall

/-!
# Lemma 10.63.2

@stack 0586
-/

@[expose] public section

/- Lemma 10.63.2 (Tag 0586): every exact-annihilator associated prime of a module lies in its
support.  The reusable statement is owned by the exact-associated-prime namespace. -/
@[stacks 0586]
#check @associatedPrimesOfModule.subset_support

/- The Mathlib-facing radical-associated-prime form and its pointwise elimination theorem are
canonical companions of the same support principle. -/
@[stacks 0586 "associated-prime set companion"]
#check @associatedPrimes.subset_support
@[stacks 0586 "pointwise support companion"]
#check @IsAssociatedPrime.mem_support
