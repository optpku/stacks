/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical.Diagonal.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Equivalence

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

/-- The product-slice diagonal equivalence assembled from the explicit swap, diagonal,
domain-change, and leg-change equivalences. Its inverse, unit, and counit are the composites
of the corresponding step data. -/
noncomputable def Diagonal.equivalence
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    gV ⊡ gU ≌
      (RightVertical.functor (RightVertical.baseIso eU eV)) ⊡
        (Δₚ xp) :=
  (CategoricalPullback.swap.equivalence gV gU).trans
    ((CategoricalPullback.DiagonalComparison.equivalence gU gV xp).trans
      ((CategoricalPullback.DomainChange.Left.equivalence
          (CategoricalPullback.LegChange.equivalence eU.symm eV.symm)
          (CategoricalPullback.toDiagonal gU gV xp) (Δₚ xp)).symm.trans
        ((CategoricalPullback.DomainChange.Left.equivalence
            (CategoricalPullback.ProductSlice.equivalence U V).symm
            ((CategoricalPullback.LegChange.equivalence eU.symm eV.symm).functor ⋙
              CategoricalPullback.toDiagonal gU gV xp)
            (Δₚ xp)).symm.trans
          (CategoricalPullback.LegChange.equivalence
            (RightVertical.comparisonIso eU eV).symm (Iso.refl (Δₚ xp))).symm)))

/-- The forward functor of the product-slice diagonal equivalence is the canonical comparison
functor. -/
@[simp]
theorem Diagonal.equivalence.functor
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    (Diagonal.equivalence eU eV).functor =
      Diagonal.comparison eU eV := rfl

/-- The underlying functor of the product-slice diagonal over-base comparison is an
equivalence. -/
instance Diagonal.comparisonOverBase.isEquivalence
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    (Diagonal.comparisonOverBase eU eV).functor.IsEquivalence :=
  (Diagonal.equivalence eU eV).isEquivalence_functor

/-- The product-slice diagonal comparison is an equivalence. -/
instance Diagonal.comparison.isEquivalence
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    (Diagonal.comparison eU eV).IsEquivalence :=
  (Diagonal.equivalence eU eV).isEquivalence_functor

end RightVertical

end Limits.CategoricalPullback.ProductSlice

end CategoryTheory
