/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Defs.Filter
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

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
  Iff.rfl

namespace minimalSpecializationPoints

/-- A minimal specialization point of `T` belongs to `T`. -/
theorem subset (T : Set (Points X)) : X.minimalSpecializationPoints T ⊆ T :=
  fun _ hx ↦ hx.1

/-- A point of `X.minimalSpecializationPoints T` admits no other point of `T`
specializing to it. -/
theorem eq_of_mem_of_specializes {T : Set (Points X)} {x y : Points X}
    (hx : x ∈ X.minimalSpecializationPoints T) (hy : y ∈ T)
    (h : Specializes y x) : y = x :=
  hx.2 hy h

/-- Specializations among points of `X.minimalSpecializationPoints T` are trivial. -/
theorem eq_of_specializes {T : Set (Points X)} {x₁ x₂ : Points X}
    (hx₁ : x₁ ∈ X.minimalSpecializationPoints T)
    (hx₂ : x₂ ∈ X.minimalSpecializationPoints T)
    (h : Specializes x₁ x₂) : x₁ = x₂ :=
  eq_of_mem_of_specializes X hx₂ (subset X T hx₁) h

end minimalSpecializationPoints

end AlgebraicGeometry.AlgebraicSpace
