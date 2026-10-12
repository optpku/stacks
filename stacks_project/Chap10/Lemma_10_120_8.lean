/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import StacksCheckRecall

/-!
# The ACCP property in a unique factorization domain

@stack 0BUD
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/- Lemma 10.120.8 (Stacks `0BUD`): a UFD satisfies the ascending-chain condition on
principal ideals. -/
@[stacks 0BUD]
#check (Ideal.setOf_isPrincipal_wellFoundedOn_gt (α := R) :
  {I : Ideal R | I.IsPrincipal}.WellFoundedOn (· > ·))

@[stacks 0BUD "well-founded principal divisibility"]
#check @WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt
