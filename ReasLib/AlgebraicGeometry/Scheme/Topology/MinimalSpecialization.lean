/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Minimal specialization points of a subset of a scheme

This file defines the points of a subset that admit no strict generalization
inside that subset and records their basic properties for Noetherian schemes.
-/

@[expose] public section

open Set TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

section

variable (S : Scheme.{u})

/-- The subset of `T` consisting of points with no strict generalization inside `T`. -/
def minimalSpecializationPoints (T : Set S) : Set S :=
  { t | t ∈ T ∧ ∀ ⦃t' : S⦄, t' ∈ T → t' ⤳ t → t' = t }

/-- Membership in `S.minimalSpecializationPoints T` means belonging to `T` and admitting no other
point of `T` specializing to it. -/
theorem mem_minimalSpecializationPoints_iff {T : Set S} {t : S} :
    t ∈ S.minimalSpecializationPoints T ↔
      t ∈ T ∧ ∀ ⦃t' : S⦄, t' ∈ T → t' ⤳ t → t' = t := Iff.rfl

namespace minimalSpecializationPoints

variable {S}

/-- A minimal specialization point of `T` belongs to `T`. -/
theorem subset (T : Set S) : S.minimalSpecializationPoints T ⊆ T := by
  intro t ht
  exact (mem_minimalSpecializationPoints_iff S).1 ht |>.1

/-- A point of `S.minimalSpecializationPoints T` admits no other point of `T` specializing to it. -/
theorem eq_of_mem_of_specializes {T : Set S} {t t' : S}
    (ht : t ∈ S.minimalSpecializationPoints T) (ht' : t' ∈ T) (h : t' ⤳ t) : t' = t :=
  (mem_minimalSpecializationPoints_iff S).1 ht |>.2 ht' h

/-- Specializations among points of `S.minimalSpecializationPoints T` are trivial. -/
theorem eq_of_specializes {T : Set S} {t₁ t₂ : S}
    (ht₁ : t₁ ∈ S.minimalSpecializationPoints T)
    (ht₂ : t₂ ∈ S.minimalSpecializationPoints T) (h : t₁ ⤳ t₂) : t₁ = t₂ :=
  eq_of_mem_of_specializes ht₂ (subset T ht₁) h

end minimalSpecializationPoints

/-- Every point of a subset of a Noetherian scheme is a specialization of a minimal
specialization point of that subset. -/
theorem exists_mem_minimalSpecializationPoints_specializingTo
    [AlgebraicGeometry.IsNoetherian S] {T : Set S} {t : S} (ht : t ∈ T) :
    ∃ t₀ ∈ S.minimalSpecializationPoints T, t₀ ⤳ t := sorry

/-- A subset of a Noetherian scheme and its minimal specialization points have the same closure. -/
theorem closure_eq_closure_minimalSpecializationPoints
    [AlgebraicGeometry.IsNoetherian S] {T : Set S} :
    closure T = closure (S.minimalSpecializationPoints T) := sorry

end

end AlgebraicGeometry.Scheme
