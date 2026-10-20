/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Descent of stacks in setoids along an fppf algebraic-space cover

The stack-in-setoids condition descends along a surjective, flat, locally finitely
presented morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace CategoryTheory.IsStack.InSetoids

/-- Let `X` be a stack in groupoids over `(Sch/S)_fppf`, let `Y` and `Z` be
algebraic spaces over `S`, and let `f : X ⟶ Z.toGroupoids` be a 1-morphism.
If `φ : Y ⟶ Z` is surjective, flat, and locally of finite presentation, and the
2-fibre product `Y ×_Z X` is a stack in setoids, then `X` is a stack in setoids. -/
@[stacks 05XL]
theorem of_fppfAlgebraicSpacePullback
    {S : Scheme.{u}} {X : GroupoidsOver S} {Y Z : AlgebraicSpace S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    (f : X ⟶ Z.toGroupoids) (φ : Y ⟶ Z)
    [AlgebraicSpace.Surjective φ] [AlgebraicSpace.Flat φ]
    [AlgebraicSpace.LocallyOfFinitePresentation φ]
    [IsStack.InSetoids (Scheme.fppfTopology.over S)
      (FiberedCategoryOver.Groupoids.p
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
          (AlgebraicSpace.toGroupoids.map φ)
          f))] :
    IsStack.InSetoids (Scheme.fppfTopology.over S) X.p :=
  sorry

end CategoryTheory.IsStack.InSetoids
