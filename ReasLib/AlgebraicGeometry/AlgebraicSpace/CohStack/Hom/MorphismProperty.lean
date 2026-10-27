/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Representable

/-!
# Morphism properties tested on algebraic-space representations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `Over S`, in
the Hom-universe of `CohStack.toGroupoids`, has a morphism property `P` of
algebraic spaces when every scheme-slice representing morphism
`fy : Fy ⟶ AlgebraicSpace.ofOver U` satisfies `P`. -/
def has {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y) : Prop :=
  ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y) (Fy : AlgebraicSpace S)
    (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    Classifying.RepresentsBaseChange f y Fy fy → P fy

/-- A 1-morphism has `P` if and only if every scheme-slice representing morphism
of algebraic spaces has `P`. -/
theorem has_iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y) :
    has P f ↔
      ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        Classifying.RepresentsBaseChange f y Fy fy → P fy := sorry

namespace has

/-- A scheme-slice representing morphism of algebraic spaces for a 1-morphism
that has `P` itself has `P`. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    {P : MorphismProperty (AlgebraicSpace S)} {f : X ⟶ Y} (hf : has P f)
    {U : Over S} (y : Classifying.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : Classifying.RepresentsBaseChange f y Fy fy) : P fy := sorry

/-- A 1-morphism has `P` if every scheme-slice representing morphism of algebraic
spaces has `P`. -/
theorem of {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    {P : MorphismProperty (AlgebraicSpace S)} {f : X ⟶ Y}
    (h : ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y) (Fy : AlgebraicSpace S)
      (fy : Fy ⟶ AlgebraicSpace.ofOver U),
      Classifying.RepresentsBaseChange f y Fy fy → P fy) : has P f := sorry

end has

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
