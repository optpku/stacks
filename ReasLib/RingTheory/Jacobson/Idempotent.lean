/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Jacobson.Ideal
public import ReasLib.Algebra.Group.Idempotent.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Idempotents modulo ideals in the Jacobson radical

@stack 09XF

Reduction modulo an ideal contained in the Jacobson radical is injective on idempotent elements.
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A]

/-- Lemma 15.10.2 (Stacks `09XF`): if `I ≤ Ring.jacobson A`, then reduction modulo `I`
is injective on idempotent elements. -/
@[stacks 09XF]
theorem quotientMk_injective_on_idempotents_of_le_jacobson (I : Ideal A)
    (hI : I ≤ Ring.jacobson A) :
    Function.Injective (Ideal.Quotient.mk I).idempotentMap := sorry
