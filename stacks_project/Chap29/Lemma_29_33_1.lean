/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Affine

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.33.1: for a ring map `R ⟶ A`, taking global sections induces a bijection from
order-`k` relative differential operators between module sheaves on `Spec A` to order-`k`
differential operators between their global-sections modules, provided the source sheaf is
quasicoherent. -/
@[stacks 0G44] #check
  (AlgebraicGeometry.Scheme.Modules.AffineDifferentialOperator.globalSections_bijective :
    ∀ {R A : CommRingCat.{u}} (φ : R ⟶ A) (ℱ 𝒢 : (Spec A).Modules)
      [ℱ.IsQuasicoherent] (k : ℕ),
      Function.Bijective
        (AlgebraicGeometry.Scheme.Modules.AffineDifferentialOperator.globalSections φ ℱ 𝒢 k))
