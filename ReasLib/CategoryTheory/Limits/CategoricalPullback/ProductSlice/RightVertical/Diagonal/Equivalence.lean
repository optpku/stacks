/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical.Diagonal.Basic

/-!
# Equivalence API for the product-slice diagonal comparison

This file owns the equivalence instances and the bundled equivalence associated with the
product-slice diagonal comparison.
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

/-- The underlying functor of the product-slice diagonal over-base comparison is an
equivalence. -/
instance Diagonal.comparisonOverBase.isEquivalence
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    (Diagonal.comparisonOverBase eU eV).functor.IsEquivalence := sorry
/- Proof strategy: unfold `Diagonal.comparisonOverBase`; each swap, diagonal comparison,
domain congruence, and leg congruence is an equivalence, and
`Functor.OverIso.compFunctorIsEquivalence` combines the five steps. -/

/-- The product-slice diagonal comparison is an equivalence. -/
instance Diagonal.comparison.isEquivalence
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    (Diagonal.comparison eU eV).IsEquivalence := sorry
/- Proof strategy: unfold `Diagonal.comparison` and
`Diagonal.comparisonOverBase`; each swap, diagonal comparison, domain congruence, and
leg congruence is an equivalence, so infer the composite instance. -/

/-- The product-slice diagonal comparison, bundled as its canonical equivalence. -/
noncomputable def Diagonal.equivalence
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    gV ⊡ gU ≌
      (RightVertical.functor (RightVertical.baseIso eU eV)) ⊡
        (Δₚ xp) :=
  (Diagonal.comparisonOverBase eU eV).asEquivalence

/-- The forward functor of the product-slice diagonal equivalence is the canonical comparison
functor. -/
@[simp]
theorem Diagonal.equivalence.functor
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    (Diagonal.equivalence eU eV).functor =
      Diagonal.comparison eU eV := sorry

end RightVertical

end Limits.CategoricalPullback.ProductSlice

end CategoryTheory
