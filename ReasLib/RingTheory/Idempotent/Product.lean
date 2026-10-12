/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.RingTheory.Idempotents

@[expose] public section

universe u

namespace RingEquiv

/-- A commutative ring decomposes as a product of two nontrivial rings exactly when it has a
nontrivial idempotent. -/
theorem exists_prod_nontrivial_iff {A : Type u} [CommRing A] :
    (∃ (B : Type u) (C : Type u) (_ : CommRing B) (_ : CommRing C),
      Nontrivial B ∧ Nontrivial C ∧ Nonempty (A ≃+* B × C)) ↔
      ∃ e : A, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := sorry

end RingEquiv
