/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.LocallyOfFinitePresentation

/-!
# Local finite presentation of lifted groupoid fibrations

Typed compatibility checks for the shared mathematical API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.LocallyOfFinitePresentation :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.locallyOfFinitePresentation_iff :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y),
    LocallyOfFinitePresentation f ↔
      ∃ (U V : AlgebraicSpace S) (a : Classifying.toGroupoids U ⟶ X)
        (b : Classifying.toGroupoids V ⟶ Y) (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧
          AlgebraicSpace.LocallyOfFinitePresentation h)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.LocallyOfFinitePresentation.of_toGroupoids :
  ∀ {S : Scheme.{u}} {U V : AlgebraicSpace S} (h : U ⟶ V)
    [AlgebraicSpace.LocallyOfFinitePresentation h],
    LocallyOfFinitePresentation (Classifying.toGroupoids.map h))

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.LocallyOfFinitePresentation.spec :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f],
    ∃ (U V : AlgebraicSpace S) (a : Classifying.toGroupoids U ⟶ X)
      (b : Classifying.toGroupoids V ⟶ Y) (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧
        AlgebraicSpace.LocallyOfFinitePresentation h)

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
