/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap99.Lemma_99_14_2
public import stacks_project.Chap99.Remark_99_14_5

/-!
# Polarized as a category fibred in groupoids over Spec ℤ

The forgetful functor of Polarized, composed with the identification of
`Sch_fppf` with `Sch / Spec ℤ`, is packaged as an object of `GroupoidsOver specZ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The forgetful functor of Polarized, viewed in `Sch / Spec ℤ`, is fibred in
groupoids. -/
instance instIsFiberedInGroupoids_toOverSpecZ :
    Functor.IsFibered.InGroupoids (p ⋙ toOverSpecZ) :=
  sorry

/-- Polarized, bundled as a category fibred in groupoids over `Sch / Spec ℤ`. -/
def toGroupoidsOverSpecZ : GroupoidsOver specZ :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u} (p ⋙ toOverSpecZ)

/-- The projection of `toGroupoidsOverSpecZ` is `p ⋙ toOverSpecZ`. -/
theorem toGroupoidsOverSpecZ_p :
    toGroupoidsOverSpecZ.p = p ⋙ toOverSpecZ :=
  sorry

/-- `toGroupoidsOverSpecZ` is the groupoid fibration associated to
`p ⋙ toOverSpecZ`. -/
theorem toGroupoidsOverSpecZ_spec :
    toGroupoidsOverSpecZ =
      FiberedCategoryOver.Groupoids.ofFunctor (p ⋙ toOverSpecZ) :=
  sorry

end AlgebraicGeometry.Polarized

