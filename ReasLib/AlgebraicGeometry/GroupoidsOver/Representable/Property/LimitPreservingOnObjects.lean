/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids

/-!
# Checking morphism properties using limit preservation on objects

For representable morphisms of categories fibred in groupoids with target limit
preserving on objects, base-change-stable, fppf-local properties can be tested
over affine schemes locally of finite presentation over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor.Fiber
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.YonedaSlice
open AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A morphism of categories fibred in groupoids representable by algebraic
spaces has a base-change-stable, fppf-local property if its target is limit
preserving on objects and every representing projection associated to a fibre
object over an affine scheme locally of finite presentation over the base has
the property. -/
@[stacks 07WI]
theorem has.of_limitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Y)]
    (h : ∀ (V : Over S) [IsAffine V.left] [LocallyOfFinitePresentation V.hom]
      (y : Y.p.Fiber V) (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver V),
      RepresentsBaseChange f (YonedaSlice.representative y) Fy fy → P fy) :
    has P f :=
  sorry

/-- A morphism of categories fibred in groupoids representable by algebraic
spaces has a base-change-stable, fppf-local property if its target is limit
preserving on objects and every representing projection associated to a slice
morphism over an affine scheme locally of finite presentation over the base has
the property. -/
theorem has.of_limitPreservingOnObjects_slice {S : Scheme.{u}}
    {X Y : GroupoidsOver S} (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Y)]
    (h : ∀ (V : Over S) [IsAffine V.left] [LocallyOfFinitePresentation V.hom]
      (y : GroupoidsOver.slice V ⟶ Y) (Fy : AlgebraicSpace S)
      (fy : Fy ⟶ ofOver V), RepresentsBaseChange f y Fy fy → P fy) :
    has P f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
