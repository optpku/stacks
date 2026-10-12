/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

universe u

namespace Ideal

/-- An element of the square of an ideal is a finite sum of products of two
elements of that ideal. -/
theorem exists_sum_mul_of_mem_sq {R : Type u} [CommRing R] {I : Ideal R} {x : R}
    (hx : x ∈ I ^ 2) :
    ∃ (t : ℕ) (f g : Fin t → R),
      (∀ i, f i ∈ I) ∧ (∀ i, g i ∈ I) ∧ x = ∑ i, f i * g i :=
  sorry

end Ideal
