/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

universe u

/- Algebraicity for lifted groupoid fibrations over a scheme. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.AlgebraicStack :
  ∀ {S : Scheme.{u}},
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) → Prop)

/- The canonical morphism to the lifted identity slice. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.toIdentitySlice :
  ∀ {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)),
    X ⟶ Classifying.slice (Over.mk (𝟙 S)))

/- The canonical diagonal of a lifted groupoid fibration. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.diagonal :
  ∀ {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)),
    X ⟶ CategoryTheory.TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1}
      (AlgebraicGeometry.AlgebraicSpace.CohStack.toIdentitySlice X)
      (AlgebraicGeometry.AlgebraicSpace.CohStack.toIdentitySlice X))
