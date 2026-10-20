/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Category
import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison.Minus
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u w

variable (X : Scheme.{u}) [IsNoetherian X]
variable [HasDerivedCategory.{w} (Scheme.QCoh X)]
variable [HasDerivedCategory.{w} (Scheme.QCoh.isCoherent X).FullSubcategory]

/- Lemma 36.11.1: for a Noetherian scheme `X`, the canonical functor
`D⁻(Coh(𝒪_X)) ⥤ D⁻_Coh(QCoh(𝒪_X))` is an equivalence. -/
@[stacks 0FDA] #check
  (CategoryTheory.DerivedCategory.Minus.CohomologyIn.Comparison.isEquivalence
    (P := AlgebraicGeometry.Scheme.QCoh.isCoherent X) :
    CategoryTheory.Functor.IsEquivalence
      (CategoryTheory.DerivedCategory.Minus.CohomologyIn.Comparison.functor
        (AlgebraicGeometry.Scheme.QCoh.isCoherent X)))
