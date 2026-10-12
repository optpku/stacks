/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed
public import ReasLib.RingTheory.Henselian.PairCriteria
public import ReasLib.RingTheory.Jacobson.Idempotent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Henselian ideals in absolutely integrally closed rings

@stack 0DCT

For an absolutely integrally closed ring, the henselian condition is detected by the Jacobson
condition and reduction of idempotents.
-/

@[expose] public section

universe u

namespace Ideal

variable {A : Type u} [CommRing A] [IsAbsolutelyIntegrallyClosed A]

/-- Lemma 15.14.8 (Stacks `0DCT`): an ideal in an absolutely integrally closed ring is henselian
exactly when it lies in the Jacobson radical and reduction induces a bijection on idempotents. -/
@[stacks 0DCT]
theorem henselianRing_iff_le_jacobson_and_bijective_on_idempotents (I : Ideal A) :
    HenselianRing A I ↔
      I ≤ Ring.jacobson A ∧ Function.Bijective (Ideal.Quotient.mk I).idempotentMap := sorry

/-- Under the Jacobson condition, injectivity on idempotents is automatic, so the criterion may
equivalently be stated using only surjectivity. -/
theorem henselianRing_iff_le_jacobson_and_surjective_on_idempotents (I : Ideal A) :
    HenselianRing A I ↔
      I ≤ Ring.jacobson A ∧ Function.Surjective (Ideal.Quotient.mk I).idempotentMap := sorry

end Ideal
