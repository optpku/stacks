/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory

/-!
# Categories of algebraic spaces fibred in groupoids

Finite-type algebraic spaces over schemes, with cartesian squares as morphisms,
and their finite-presentation, flat, proper full subcategory are fibred in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- Finite-type algebraic spaces over schemes over `S`, with cartesian squares
as morphisms, form a category fibred in groupoids over `Over S`. -/
@[stacks 0D1E]
instance FtGroupoids.instIsFiberedInGroupoids (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids (pFtGroupoids S) := sorry

/-- The full subcategory of finite-presentation, flat, proper objects in
`FtGroupoids S` is fibred in groupoids over `Over S`. -/
@[stacks 0D1E]
instance FpFlatProperGroupoids.instIsFiberedInGroupoids (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids (pFpFlatProperGroupoids S) := sorry

/-- Finite-type algebraic spaces with cartesian squares as morphisms, bundled
as a category fibred in groupoids over `Over S` with Hom universe `u + 1`. -/
def FtGroupoids.toGroupoids (S : Scheme.{u}) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1}
    (pFtGroupoids S)

/-- The projection of `FtGroupoids.toGroupoids S` is `pFtGroupoids S`. -/
theorem FtGroupoids.toGroupoids_p (S : Scheme.{u}) :
    (FtGroupoids.toGroupoids S).p = pFtGroupoids S := rfl

/-- Finite-presentation, flat, proper algebraic spaces with cartesian squares
as morphisms, bundled as a category fibred in groupoids over `Over S`. -/
def FpFlatProperGroupoids.toGroupoids (S : Scheme.{u}) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1}
    (pFpFlatProperGroupoids S)

/-- The projection of `FpFlatProperGroupoids.toGroupoids S` is
`pFpFlatProperGroupoids S`. -/
theorem FpFlatProperGroupoids.toGroupoids_p (S : Scheme.{u}) :
    (FpFlatProperGroupoids.toGroupoids S).p = pFpFlatProperGroupoids S := rfl

end AlgebraicGeometry.AlgebraicSpace.Spaces
