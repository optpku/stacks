/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Finite square-cube-or-prime-power adjunctions of subrings

This module records the condition that finite subsets of a commutative ring can be captured by
successively adjoining elements satisfying a square-cube or prime-power condition over the
previously generated subring.
-/

@[expose] public section

universe u

namespace Subring

variable {B : Type u} [CommRing B]

/-- Every finite subset of `B` is contained in a subring obtained from `A` by finitely many
successive adjunctions, where each new generator has either its square and cube in the preceding
subring or, for some prime `p`, both its multiple by `p` and its `p`-th power there. -/
def IsFilteredBySquareCubeOrPrimePowerAdjunctions (A : Subring B) : Prop :=
  ∀ E : Finset B, ∃ (n : ℕ) (b : Fin n → B),
    (∀ i : Fin n,
      (b i ^ 2 ∈
            Subring.closure
              ((A : Set B) ∪
                Set.range (fun j : Fin i.val ↦ b ⟨j, Nat.lt_trans j.isLt i.isLt⟩)) ∧
          b i ^ 3 ∈
            Subring.closure
              ((A : Set B) ∪
                Set.range (fun j : Fin i.val ↦ b ⟨j, Nat.lt_trans j.isLt i.isLt⟩))) ∨
        ∃ p : ℕ, Nat.Prime p ∧
          (p : B) * b i ∈
              Subring.closure
                ((A : Set B) ∪
                  Set.range (fun j : Fin i.val ↦ b ⟨j, Nat.lt_trans j.isLt i.isLt⟩)) ∧
            b i ^ p ∈
              Subring.closure
                ((A : Set B) ∪
                  Set.range (fun j : Fin i.val ↦ b ⟨j, Nat.lt_trans j.isLt i.isLt⟩))) ∧
      ∀ e ∈ E, e ∈ Subring.closure ((A : Set B) ∪ Set.range b)

/-- The pointwise finite-generator characterization of mixed square-cube-or-prime-power filtered
adjunctions. -/
theorem isFilteredBySquareCubeOrPrimePowerAdjunctions_iff (A : Subring B) :
    IsFilteredBySquareCubeOrPrimePowerAdjunctions A ↔
      ∀ E : Finset B, ∃ (n : ℕ) (b : Fin n → B),
        (∀ i : Fin n,
          (b i ^ 2 ∈
                Subring.closure
                  ((A : Set B) ∪
                    Set.range (fun j : Fin i.val ↦ b ⟨j, Nat.lt_trans j.isLt i.isLt⟩)) ∧
              b i ^ 3 ∈
                Subring.closure
                  ((A : Set B) ∪
                    Set.range (fun j : Fin i.val ↦ b ⟨j, Nat.lt_trans j.isLt i.isLt⟩))) ∨
            ∃ p : ℕ, Nat.Prime p ∧
              (p : B) * b i ∈
                  Subring.closure
                    ((A : Set B) ∪
                      Set.range (fun j : Fin i.val ↦ b ⟨j, Nat.lt_trans j.isLt i.isLt⟩)) ∧
                b i ^ p ∈
                  Subring.closure
                    ((A : Set B) ∪
                      Set.range (fun j : Fin i.val ↦ b ⟨j, Nat.lt_trans j.isLt i.isLt⟩))) ∧
          ∀ e ∈ E, e ∈ Subring.closure ((A : Set B) ∪ Set.range b) := Iff.rfl

end Subring
