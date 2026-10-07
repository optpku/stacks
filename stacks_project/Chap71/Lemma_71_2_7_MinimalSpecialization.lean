module

public import Mathlib.Topology.Defs.Filter
public import stacks_project.Chap66.Lemma_66_4_6_Topology

/-!
# Minimal specialization points of a subset of an algebraic space

This file defines the points of a subset of `|X|` that admit no strict
generalization inside that subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The subset of `T` consisting of points of `|X|` with no strict generalization
inside `T`. -/
def minimalSpecializationPoints (T : Set (Points X)) : Set (Points X) :=
  {x | x ∈ T ∧ ∀ ⦃y : Points X⦄, y ∈ T → Specializes y x → y = x}

/-- Membership in `X.minimalSpecializationPoints T` means belonging to `T` and
admitting no other point of `T` specializing to it. -/
theorem mem_minimalSpecializationPoints_iff {T : Set (Points X)} {x : Points X} :
    x ∈ X.minimalSpecializationPoints T ↔
      x ∈ T ∧ ∀ ⦃y : Points X⦄, y ∈ T → Specializes y x → y = x :=
  sorry

namespace minimalSpecializationPoints

/-- A minimal specialization point of `T` belongs to `T`. -/
theorem subset (T : Set (Points X)) : X.minimalSpecializationPoints T ⊆ T :=
  sorry

/-- A point of `X.minimalSpecializationPoints T` admits no other point of `T`
specializing to it. -/
theorem eq_of_mem_of_specializes {T : Set (Points X)} {x y : Points X}
    (hx : x ∈ X.minimalSpecializationPoints T) (hy : y ∈ T)
    (h : Specializes y x) : y = x :=
  sorry

/-- Specializations among points of `X.minimalSpecializationPoints T` are trivial. -/
theorem eq_of_specializes {T : Set (Points X)} {x₁ x₂ : Points X}
    (hx₁ : x₁ ∈ X.minimalSpecializationPoints T)
    (hx₂ : x₂ ∈ X.minimalSpecializationPoints T)
    (h : Specializes x₁ x₂) : x₁ = x₂ :=
  sorry

end minimalSpecializationPoints

end AlgebraicGeometry.AlgebraicSpace
