/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap99.Lemma_99_14_2_Forget

/-!
# Lemma 99.14.2

The category Polarized is fibred in groupoids over
`Spaces'_{fp, flat, proper}` and over `Sch_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces hiding p

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Lemma 99.14.2 (1): Polarized is fibred in groupoids over
`Spaces'_{fp, flat, proper}` via the forgetful functor `toFpFlatProper`. -/
@[stacks 0D3Z]
instance instIsFiberedInGroupoids_toFpFlatProper :
    Functor.IsFibered.InGroupoids toFpFlatProper :=
  sorry

/-- Lemma 99.14.2 (2): Polarized is fibred in groupoids over `Sch_fppf` via the
forgetful functor `p`. -/
@[stacks 0D3Z]
instance instIsFiberedInGroupoids : Functor.IsFibered.InGroupoids p :=
  sorry

/-- Polarized, bundled as a category fibred in groupoids over `Sch_fppf`. The
Hom-universe is `u`, matching `Polarized.over`. -/
def toGroupoids : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} Scheme.{u} :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u} p

/-- The projection of `toGroupoids` is the forgetful functor `p`. -/
theorem toGroupoids_p : toGroupoids.p = p :=
  sorry

end AlgebraicGeometry.Polarized
