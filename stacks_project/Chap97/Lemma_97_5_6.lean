/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property.LimitPreservingOnObjects
import StacksCheckRecall

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

/- Lemma 97.5.6: A representable morphism with target limit preserving on
objects has a base-change-stable, fppf-local property whenever all affine
locally finite-presentation fibre-object tests have that property. -/
@[stacks 07WI] #check (AlgebraicGeometry.Groupoids.Hom.has.of_limitPreservingOnObjects :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Y)]
    (h : ∀ (V : Over S) [IsAffine V.left] [LocallyOfFinitePresentation V.hom]
      (y : Y.p.Fiber V) (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver V),
      RepresentsBaseChange f (YonedaSlice.representative y) Fy fy → P fy),
    has P f)

#check (AlgebraicGeometry.Groupoids.Hom.has.of_limitPreservingOnObjects_slice :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Y)]
    (h : ∀ (V : Over S) [IsAffine V.left] [LocallyOfFinitePresentation V.hom]
      (y : GroupoidsOver.slice V ⟶ Y) (Fy : AlgebraicSpace S)
      (fy : Fy ⟶ ofOver V), RepresentsBaseChange f y Fy fy → P fy),
    has P f)

end AlgebraicGeometry.Groupoids.Hom
