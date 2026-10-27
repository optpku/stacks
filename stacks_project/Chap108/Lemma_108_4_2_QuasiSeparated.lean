/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.QuasiSeparated

/-!
# Quasi-separated morphisms of lifted groupoid fibrations

Typed compatibility checks for the shared mathematical API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.has :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.has_iff :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y),
    has P f ↔
      ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        Classifying.RepresentsBaseChange f y Fy fy → P fy)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.has.spec :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    {P : MorphismProperty (AlgebraicSpace S)} {f : X ⟶ Y} (hf : has P f)
    {U : Over S} (y : Classifying.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : Classifying.RepresentsBaseChange f y Fy fy),
    P fy)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.has.of :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    {P : MorphismProperty (AlgebraicSpace S)} {f : X ⟶ Y}
    (h : ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y) (Fy : AlgebraicSpace S)
      (fy : Fy ⟶ AlgebraicSpace.ofOver U),
      Classifying.RepresentsBaseChange f y Fy fy → P fy),
    has P f)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.QuasiSeparated :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.QuasiSeparated.id :
  ∀ {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)},
    QuasiSeparated (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.QuasiSeparated.iff :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y),
    QuasiSeparated f ↔
      Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal f) ∧
        has (@AlgebraicSpace.QuasiCompact S) (diagonal f) ∧
          has (@AlgebraicSpace.QuasiSeparated S) (diagonal f))

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.QuasiSeparated.spec :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [QuasiSeparated f],
    Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal f) ∧
      has (@AlgebraicSpace.QuasiCompact S) (diagonal f) ∧
        has (@AlgebraicSpace.QuasiSeparated S) (diagonal f))

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
