/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.LocallyOfFinitePresentation

/-!
# The canonical topology on points of lifted algebraic stacks

Openness is tested along flat, locally finitely presented morphisms from algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

namespace Points

variable {S : Scheme.{u}}
  {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
  [AlgebraicStack X]

/-- A set of points of `X` is open when its preimage along every flat
locally-of-finite-presentation map from an algebraic space is open. -/
def isOpen (s : Set (Points X)) : Prop :=
  ∀ ⦃U : AlgebraicSpace S⦄ (p : Classifying.toGroupoids U ⟶ X)
    [Hom.Flat p] [Hom.LocallyOfFinitePresentation p],
    IsOpen (mapSpace p ⁻¹' s)

/-- The predicate `isOpen` is the final-openness condition along flat
locally-of-finite-presentation maps from algebraic spaces. -/
theorem isOpen_eq (s : Set (Points X)) :
    isOpen s ↔
      ∀ ⦃U : AlgebraicSpace S⦄ (p : Classifying.toGroupoids U ⟶ X)
        [Hom.Flat p] [Hom.LocallyOfFinitePresentation p],
        IsOpen (mapSpace p ⁻¹' s) :=
  Iff.rfl

/-- The universal set satisfies the canonical openness test. -/
theorem isOpen_univ : isOpen (Set.univ : Set (Points X)) := sorry

/-- The intersection of two sets satisfying the canonical openness test also
satisfies that test. -/
theorem isOpen_inter (s t : Set (Points X)) (hs : isOpen s) (ht : isOpen t) :
    isOpen (s ∩ t) := sorry

/-- A union of sets satisfying the canonical openness test satisfies that test. -/
theorem isOpen_sUnion (s : Set (Set (Points X))) (hs : ∀ t ∈ s, isOpen t) :
    isOpen (⋃₀ s) := sorry

end Points

/-- The canonical topology on the points of an algebraic stack over `S` in the
Hom-universe of `CohStack.toGroupoids`. -/
instance instTopologicalSpacePoints {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
    [AlgebraicStack X] : TopologicalSpace (Points X) where
  IsOpen := Points.isOpen
  isOpen_univ := Points.isOpen_univ
  isOpen_inter := Points.isOpen_inter
  isOpen_sUnion := Points.isOpen_sUnion

namespace Points

variable {S : Scheme.{u}}
  {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
  [AlgebraicStack X]

/-- Open sets in the canonical topology are those whose preimages along every
flat locally-of-finite-presentation map from an algebraic space are open. -/
theorem isOpen_iff (s : Set (Points X)) :
    IsOpen s ↔
      ∀ ⦃U : AlgebraicSpace S⦄ (p : Classifying.toGroupoids U ⟶ X)
        [Hom.Flat p] [Hom.LocallyOfFinitePresentation p],
        IsOpen (mapSpace p ⁻¹' s) :=
  Iff.rfl

/-- Every 1-morphism of algebraic stacks over `S` induces a continuous map on
points. -/
theorem continuous_map
    {Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack Y] (f : X ⟶ Y) : Continuous (map f) :=
  sorry

end Points

end AlgebraicGeometry.AlgebraicSpace.CohStack
