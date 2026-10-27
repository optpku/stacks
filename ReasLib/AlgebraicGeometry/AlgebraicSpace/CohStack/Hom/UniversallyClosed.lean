/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Points.Topology

/-!
# Universally closed morphisms of lifted groupoid fibrations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open AlgebraicGeometry.AlgebraicSpace.CohStack (AlgebraicStack Points)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism `f : X ⟶ Y` of algebraic stacks over `S`, in the Hom-universe
of `CohStack.toGroupoids`, is universally closed if every 2-fibre-product base
change induces a closed map on underlying point spaces. -/
@[mk_iff]
class UniversallyClosed {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The second projection of every 2-fibre product of `f` is a closed map on
  points. -/
  closed_snd {Z : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
      [AlgebraicStack Z] (g : Z ⟶ Y)
      [AlgebraicStack
        (CategoryTheory.TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1} f g)] :
    IsClosedMap
      (Points.map
        (CategoryTheory.TwoFibreProduct.snd.{u + 1, u, u + 1, u + 1} f g))

namespace UniversallyClosed

/-- The identity 1-morphism of an algebraic stack is universally closed. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] : UniversallyClosed (𝟙 X) :=
  sorry

/-- A universally closed 1-morphism has closed 2-fibre-product projections on
points. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [UniversallyClosed f]
    {Z : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack Z] (g : Z ⟶ Y)
    [AlgebraicStack
      (CategoryTheory.TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1} f g)] :
    IsClosedMap
      (Points.map
        (CategoryTheory.TwoFibreProduct.snd.{u + 1, u, u + 1, u + 1} f g)) :=
  sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
