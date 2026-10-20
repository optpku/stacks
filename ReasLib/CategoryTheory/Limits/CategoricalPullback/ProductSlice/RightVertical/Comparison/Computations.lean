module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical.Comparison

/-!
# Computations for the right-vertical comparison

The forward and inverse comparison components are identities on both categorical-pullback
projections.
-/

@[expose] public section

universe vC vXS uC uXS

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace Limits.CategoricalPullback.ProductSlice

section RightVertical

variable {C : Type uC} [Category.{vC} C] [Limits.HasBinaryProducts C]
variable {XS : Type uXS} [Category.{vXS} XS]
variable {U V : C} {gU : Over U ⥤ XS} {gV : Over V ⥤ XS} {xp : XS ⥤ C}

/-- The first component of the forward right-vertical comparison is the identity. -/
@[simp]
theorem RightVertical.comparisonIso.hom.app.fst
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (c : Over (Limits.prod U V)) :
    ((RightVertical.comparisonIso eU eV).hom.app c).fst = 𝟙 _ := sorry

/-- The second component of the forward right-vertical comparison is the identity. -/
@[simp]
theorem RightVertical.comparisonIso.hom.app.snd
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (c : Over (Limits.prod U V)) :
    ((RightVertical.comparisonIso eU eV).hom.app c).snd = 𝟙 _ := sorry

/-- The first component of the inverse right-vertical comparison is the identity. -/
@[simp]
theorem RightVertical.comparisonIso.inv.app.fst
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (c : Over (Limits.prod U V)) :
    ((RightVertical.comparisonIso eU eV).inv.app c).fst = 𝟙 _ := sorry

/-- The second component of the inverse right-vertical comparison is the identity. -/
@[simp]
theorem RightVertical.comparisonIso.inv.app.snd
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (c : Over (Limits.prod U V)) :
    ((RightVertical.comparisonIso eU eV).inv.app c).snd = 𝟙 _ := sorry

end RightVertical

end Limits.CategoricalPullback.ProductSlice

end CategoryTheory
