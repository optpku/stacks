/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Surjective

public import stacks_project.Chap109.Lemma_109_17_1_Points

/-!
# Surjective morphisms of CohStack-sized groupoid fibrations

A 1-morphism `f : X ⟶ Y` in `FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`
is surjective when the induced map `|X| → |Y|` on points is surjective, matching Stacks
Definition 101.5.1 (tag 04ZS) at the Hom-universe of `CohStack.toGroupoids`.

The class is stated directly on field-valued points: every field-valued point of `Y` is
equivalent to the image of a field-valued point of `X`, i.e. it lifts after passing to a
common field extension. On algebraic stacks this is surjectivity of `Points.map f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

namespace Surjective

/-- On algebraic stacks, surjectivity is surjectivity of the induced map `|X| → |Y|` of
points (Stacks Definition 101.5.1). -/
@[stacks 04ZS]
theorem iff_points_map_surjective {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Surjective f ↔ Function.Surjective (Points.map f) :=
  sorry

/-- A surjective 1-morphism of algebraic stacks induces a surjective map on points. -/
theorem points_map_surjective {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Surjective f] :
    Function.Surjective (Points.map f) :=
  sorry

/-- For a 1-morphism of algebraic stacks representable by algebraic spaces, surjectivity on
points agrees with surjectivity of every representing morphism of algebraic spaces
(Stacks Lemma 100.4.4, tag 04XI). -/
@[stacks 04XI]
theorem iff_classifying {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : Classifying.relativelyRepresentableByAlgebraicSpaces f) :
    Surjective f ↔ Classifying.Surjective f :=
  sorry

end Surjective

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
