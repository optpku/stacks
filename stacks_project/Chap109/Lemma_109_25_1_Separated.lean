/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap108.Lemma_108_4_2_QuasiSeparated

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Separated

/-!
# Separated morphisms of CohStack-sized groupoid fibrations

Typed compatibility checks for the shared separatedness API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Separated :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Separated.id :
  ∀ {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)},
    Separated (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Separated.iff :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y),
    Separated f ↔
      Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal f) ∧
        has (@AlgebraicSpace.Proper S) (diagonal f))

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Separated.spec :
  ∀ {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [Separated f],
    Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal f) ∧
      has (@AlgebraicSpace.Proper S) (diagonal f))

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
