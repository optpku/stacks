/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Representable

/-!
# Flat morphisms of CohStack-sized groupoid fibrations

A 1-morphism in `FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`
is flat when it is representable by algebraic spaces and every representing
morphism `fy : Fy ⟶ ofOver U` is a flat morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S`, in the
Hom-universe of `CohStack.toGroupoids`, is flat when it is representable by
algebraic spaces and every representing morphism `fy : Fy ⟶ ofOver U` is a
flat morphism of algebraic spaces. -/
class Flat {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : Classifying.relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is flat. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    Classifying.RepresentsBaseChange f y Fy fy → AlgebraicSpace.Flat fy

namespace Flat

/-- The identity 1-morphism of a category fibred in groupoids is flat. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    Flat (𝟙 X) := sorry

/-- A representing morphism of algebraic spaces for a flat 1-morphism of
groupoid fibrations is flat. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [Flat f] {U : Over S} (y : Classifying.slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : Classifying.RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.Flat fy := sorry

/-- A flat 1-morphism of groupoid fibrations is representable by algebraic
spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [Flat f] :
    Classifying.relativelyRepresentableByAlgebraicSpaces f := sorry

/-- A 1-morphism is flat if and only if it is representable by algebraic spaces
and every representing morphism of algebraic spaces is flat. -/
theorem iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    Flat f ↔
      Classifying.relativelyRepresentableByAlgebraicSpaces f ∧
        ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y) (Fy : AlgebraicSpace S)
          (fy : Fy ⟶ AlgebraicSpace.ofOver U),
          Classifying.RepresentsBaseChange f y Fy fy →
            AlgebraicSpace.Flat fy := sorry

end Flat

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
