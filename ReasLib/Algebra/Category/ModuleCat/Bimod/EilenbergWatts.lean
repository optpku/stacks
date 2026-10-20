/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Basic
public import ReasLib.Algebra.Category.ModuleCat.Bimod.RelativeTensor.ModuleFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Limits Module.Bimodule.RelativeTensor

namespace ModuleCat.EilenbergWatts

/-- For rings `A` and `B`, a functor between their right-module categories is tensoring
with a compatible bimodule if and only if it is right exact and preserves all direct sums,
preserves all colimits, or has a right adjoint. -/
theorem eilenbergWatts_tfae {A B : Type} [Ring A] [Ring B]
    (F : ModuleCat Aᵐᵒᵖ ⥤ ModuleCat Bᵐᵒᵖ) :
    List.TFAE
      [ ∃ (K : Type) (_ : AddCommGroup K) (_ : Module A K)
            (_ : Module Bᵐᵒᵖ K) (_ : SMulCommClass A Bᵐᵒᵖ K),
          Nonempty (F ≅
            @tensorModuleFunctor ℤ A B K _ _ _ _ _ _ _ _ _ _ _ _)
      , rightExactFunctor (ModuleCat Aᵐᵒᵖ) (ModuleCat Bᵐᵒᵖ) F ∧
          ∀ J : Type, PreservesColimitsOfShape (Discrete J) F
      , PreservesColimits F
      , F.IsLeftAdjoint ] := sorry

end ModuleCat.EilenbergWatts
