/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids

/-!
# Stacks along morphisms representable by algebraic spaces

A category fibred in groupoids with a morphism representable by algebraic spaces
to a stack in groupoids is itself a stack in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- If `f : X ⟶ Z` is representable by algebraic spaces and `Y` is a stack in
groupoids over `(Sch/S)_fppf`, then the 2-fibre product of `f` and `g : Y ⟶ Z`
is a stack in groupoids. -/
@[stacks 0CKY]
theorem relativelyRepresentableByAlgebraicSpaces.twoFibreProduct_isStack
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p] :
    IsStack.InGroupoids (Scheme.fppfTopology.over S)
      (FiberedCategoryOver.Groupoids.p
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)) := sorry

/-- If `f : X ⟶ Y` is representable by algebraic spaces and `Y` is a stack in
groupoids over `(Sch/S)_fppf`, then `X` is a stack in groupoids. -/
theorem relativelyRepresentableByAlgebraicSpaces.source_isStack
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p] :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p := sorry

end AlgebraicGeometry
