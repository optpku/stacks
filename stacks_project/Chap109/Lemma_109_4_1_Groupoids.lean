/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import stacks_project.Chap99.Lemma_99_14_8_Groupoids
public import stacks_project.Chap109.Lemma_109_4_1_PolarizedCurves

/-!
# PolarizedCurves as a category fibred in groupoids over Spec ℤ

The forgetful functor of PolarizedCurves, composed with the identification of
`Sch_fppf` with `Sch / Spec ℤ`, is packaged as an object of `GroupoidsOver specZ`,
together with the inclusion 1-morphism into Polarized.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.PolarizedCurves

/-- The forgetful functor of PolarizedCurves, viewed in `Sch / Spec ℤ`, is
fibred in groupoids. -/
instance instIsFiberedInGroupoids_toOverSpecZ :
    Functor.IsFibered.InGroupoids (p ⋙ Polarized.toOverSpecZ) :=
  sorry

/-- PolarizedCurves, bundled as a category fibred in groupoids over
`Sch / Spec ℤ`. -/
def toGroupoidsOverSpecZ : GroupoidsOver specZ :=
  Groupoids.ofFunctor.{u + 1, u, u + 1, u} (p ⋙ Polarized.toOverSpecZ)

/-- The projection of `toGroupoidsOverSpecZ` is `p ⋙ Polarized.toOverSpecZ`. -/
theorem toGroupoidsOverSpecZ_p :
    toGroupoidsOverSpecZ.p = p ⋙ Polarized.toOverSpecZ :=
  sorry

/-- The 1-morphism PolarizedCurves ⟶ Polarized, packaged as a morphism of
categories fibred in groupoids over `Spec ℤ`. The underlying functor is the
full-subcategory inclusion. -/
def inclusionHom : toGroupoidsOverSpecZ ⟶ Polarized.toGroupoidsOverSpecZ :=
  Groupoids.ofBasedFunctor
    { toFunctor := inclusion
      w := sorry }

/-- The underlying functor of `inclusionHom` is the full-subcategory
inclusion. -/
theorem inclusionHom_toFunctor :
    Groupoids.toFunctor inclusionHom = inclusion :=
  sorry

/-- `inclusionHom` lies strictly over `Sch / Spec ℤ`. -/
theorem inclusionHom_comm :
    Groupoids.toFunctor inclusionHom ⋙ Polarized.toGroupoidsOverSpecZ.p =
      toGroupoidsOverSpecZ.p :=
  sorry

end AlgebraicGeometry.PolarizedCurves
