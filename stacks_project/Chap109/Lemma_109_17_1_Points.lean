/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Points.Topology

/-!
# Points of lifted algebraic stacks

Typed compatibility checks for the canonical quotient point space and its topology.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

/- Lemma 109.17.1: the canonical space of field-valued point classes. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Points :
  ∀ {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
    [AlgebraicStack X], Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Points.map :
  ∀ {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X]
    {Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack Y], (X ⟶ Y) → Points X → Points Y)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Points.isOpen_iff :
  ∀ {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] (s : Set (Points X)),
    IsOpen s ↔
      ∀ ⦃U : AlgebraicSpace S⦄ (p : Classifying.toGroupoids U ⟶ X)
        [Hom.Flat p] [Hom.LocallyOfFinitePresentation p],
        IsOpen (Points.mapSpace p ⁻¹' s))

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Points.continuous_map :
  ∀ {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X]
    {Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack Y] (f : X ⟶ Y), Continuous (Points.map f))

end AlgebraicGeometry.AlgebraicSpace.CohStack
