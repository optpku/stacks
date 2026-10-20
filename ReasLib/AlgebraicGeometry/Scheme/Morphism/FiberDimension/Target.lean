/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.BaseChange

/-!
# Dimensions of fibres over target points

This module defines the target-indexed Krull dimension of the fibres of a
scheme morphism and records its invariance under base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The function assigning to a point of the target the topological Krull
dimension of the corresponding scheme-theoretic fibre. -/
noncomputable def fiberDimension {X Y : Scheme.{u}} (f : X ⟶ Y) : Y → WithBot ℕ∞ :=
  fun y ↦ topologicalKrullDim (f.fiber y)

/-- Evaluating `fiberDimension` gives the topological Krull dimension of the
corresponding scheme-theoretic fibre. -/
theorem fiberDimension_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    f.fiberDimension y = topologicalKrullDim (f.fiber y) := sorry

/-- The target-indexed Krull dimension of fibres is preserved by a pullback
square of finite-type scheme morphisms. -/
theorem fiberDimension_baseChange {Y X Y' X' : Scheme.{u}}
    (f : X ⟶ Y) [FiniteType f] (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) :
    f'.fiberDimension = f.fiberDimension ∘ g := sorry

end AlgebraicGeometry.Scheme.Hom
