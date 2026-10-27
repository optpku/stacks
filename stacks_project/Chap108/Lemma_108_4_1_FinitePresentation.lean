/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap110.Lemma_110_53_1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.FinitePresentation

/-!
# Finite-presentation morphisms of lifted groupoid fibrations

Typed compatibility checks for the shared mathematical API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.FinitePresentation :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.FinitePresentation.id :
  ∀ {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)},
    FinitePresentation (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.FinitePresentation.spec :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [FinitePresentation f] {U : Over S}
    (y : Classifying.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : Classifying.RepresentsBaseChange f y Fy fy),
    AlgebraicSpace.FinitePresentation fy)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.FinitePresentation.relativelyRepresentable :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [FinitePresentation f],
    Classifying.relativelyRepresentableByAlgebraicSpaces f)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.FinitePresentation.iff :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y),
    FinitePresentation f ↔
      Classifying.relativelyRepresentableByAlgebraicSpaces f ∧
        ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y) (Fy : AlgebraicSpace S)
          (fy : Fy ⟶ AlgebraicSpace.ofOver U),
          Classifying.RepresentsBaseChange f y Fy fy →
            AlgebraicSpace.FinitePresentation fy)

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
