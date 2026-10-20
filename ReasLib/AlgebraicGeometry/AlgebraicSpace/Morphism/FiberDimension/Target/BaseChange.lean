/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Target

/-!
# Base change of target-indexed fibre dimensions

The target-indexed fibre dimension of a finite type morphism of algebraic
spaces is invariant under arbitrary base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The target-indexed fibre-dimension function is invariant under base change
along a morphism of algebraic spaces. -/
theorem fiberDimension_baseChange {S : Scheme.{u}}
    {X Y Y' X' : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) :
    fiberDimension f' = fiberDimension f ∘ Points.map g :=
  sorry

/-- At each point of the new target, the fibre dimension after base change is
the original fibre dimension at its image. -/
theorem fiberDimension_baseChange_apply {S : Scheme.{u}}
    {X Y Y' X' : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) (y' : Points Y') :
    fiberDimension f' y' = fiberDimension f (Points.map g y') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
