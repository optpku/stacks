module

public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Finite square-cube adjunctions of subrings

This module records the condition that finite subsets of a commutative ring can be captured by
successively adjoining elements whose squares and cubes lie in the previously generated subring.
-/

@[expose] public section

universe u

namespace Subring

variable {B : Type u} [CommRing B]

/-- Every finite subset of `B` is contained in a subring obtained from `A` by finitely many
successive adjunctions, where the square and cube of each new generator lie in the subring
generated at the preceding stage. -/
def IsFilteredBySquareCubeAdjunctions (A : Subring B) : Prop :=
  ∀ E : Finset B, ∃ (n : ℕ) (b : Fin n → B),
    (∀ i : Fin n,
      b i ^ 2 ∈
          Subring.closure
            ((A : Set B) ∪
              Set.range (fun j : Fin i.val ↦ b ⟨j, Nat.lt_trans j.isLt i.isLt⟩)) ∧
        b i ^ 3 ∈
          Subring.closure
            ((A : Set B) ∪
              Set.range (fun j : Fin i.val ↦ b ⟨j, Nat.lt_trans j.isLt i.isLt⟩))) ∧
      ∀ e ∈ E, e ∈ Subring.closure ((A : Set B) ∪ Set.range b)

/-- The pointwise finite-generator characterization of square-cube filtered adjunctions. -/
theorem isFilteredBySquareCubeAdjunctions_iff (A : Subring B) :
    IsFilteredBySquareCubeAdjunctions A ↔
      ∀ E : Finset B, ∃ (n : ℕ) (b : Fin n → B),
        (∀ i : Fin n,
          b i ^ 2 ∈
              Subring.closure
                ((A : Set B) ∪
                  Set.range (fun j : Fin i.val ↦ b ⟨j, Nat.lt_trans j.isLt i.isLt⟩)) ∧
            b i ^ 3 ∈
              Subring.closure
                ((A : Set B) ∪
                  Set.range (fun j : Fin i.val ↦ b ⟨j, Nat.lt_trans j.isLt i.isLt⟩))) ∧
          ∀ e ∈ E, e ∈ Subring.closure ((A : Set B) ∪ Set.range b) := sorry

end Subring
