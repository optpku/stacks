module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap99.Lemma_99_13_1_Spaces

/-!
# Lemma 99.13.1

The primed categories `Spaces'_ft` and `Spaces'_{fp, flat, proper}` are fibered
in groupoids over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- Lemma 99.13.1 (1): the category `FtGroupoids S` of finite-type algebraic
spaces over schemes over `S`, with morphisms the cartesian squares, is fibered
in groupoids over `Over S`. -/
@[stacks 0D1E]
instance FtGroupoids.instIsFiberedInGroupoids (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids (pFtGroupoids S) := sorry

/-- Lemma 99.13.1 (2): the full subcategory `FpFlatProperGroupoids S` of
finite-presentation, flat, and proper objects of `FtGroupoids S` is fibered
in groupoids over `Over S`. -/
@[stacks 0D1E]
instance FpFlatProperGroupoids.instIsFiberedInGroupoids (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids (pFpFlatProperGroupoids S) := sorry

/-- The finite-type primed groupoid of algebraic spaces, bundled as a category
fibred in groupoids over `Over S`. The Hom-universe is `u + 1` because
`Category (AlgebraicSpace S)` is `Category.{u + 1}`, so this cannot land in
`GroupoidsOver S`, which pins Hom-universe `u`. -/
def FtGroupoids.toGroupoids (S : Scheme.{u}) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1}
    (pFtGroupoids S)

/-- The projection of `FtGroupoids.toGroupoids S` is `pFtGroupoids S`. -/
theorem FtGroupoids.toGroupoids_p (S : Scheme.{u}) :
    (FtGroupoids.toGroupoids S).p = pFtGroupoids S := sorry

/-- The fp-flat-proper primed groupoid of algebraic spaces, bundled as a
category fibred in groupoids over `Over S`. -/
def FpFlatProperGroupoids.toGroupoids (S : Scheme.{u}) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1}
    (pFpFlatProperGroupoids S)

/-- The projection of `FpFlatProperGroupoids.toGroupoids S` is
`pFpFlatProperGroupoids S`. -/
theorem FpFlatProperGroupoids.toGroupoids_p (S : Scheme.{u}) :
    (FpFlatProperGroupoids.toGroupoids S).p = pFpFlatProperGroupoids S := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces

