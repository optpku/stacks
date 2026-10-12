/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import stacks_project.Chap99.Lemma_99_13_1

/-!
# Lemma 99.13.3

The primed categories `Spaces'_ft` and `Spaces'_{fp, flat, proper}` are stacks
in groupoids over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- Lemma 99.13.3 (1): the category `FtGroupoids S` of finite-type algebraic
spaces over schemes over `S`, with morphisms the cartesian squares (the source
category `Spaces'_ft`), is a stack in groupoids over `(Sch/S)_fppf`. Hom-types
live in `Type (u + 1)`, so this cannot land in `GroupoidsOver S`. -/
@[stacks 0D1G]
instance FtGroupoids.instIsStackInGroupoids (S : Scheme.{u}) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (pFtGroupoids S) := sorry

/-- Lemma 99.13.3 (2): the full subcategory `FpFlatProperGroupoids S` of
finite-presentation, flat, and proper objects of `FtGroupoids S` (the source
category `Spaces'_{fp, flat, proper}`) is a stack in groupoids over
`(Sch/S)_fppf`. -/
@[stacks 0D1G]
instance FpFlatProperGroupoids.instIsStackInGroupoids (S : Scheme.{u}) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (pFpFlatProperGroupoids S) :=
  sorry

/-- The projection `pFtGroupoids S` is a stack on the site `(Sch/S)_fppf`. -/
theorem FtGroupoids.p_isStackOnSite (S : Scheme.{u}) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (pFtGroupoids S) := sorry

/-- The projection `pFpFlatProperGroupoids S` is a stack on the site
`(Sch/S)_fppf`. -/
theorem FpFlatProperGroupoids.p_isStackOnSite (S : Scheme.{u}) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (pFpFlatProperGroupoids S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
