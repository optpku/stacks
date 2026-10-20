/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Blowup
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 31.35.2: if a finite-type quasicoherent module `ℱ` is finite locally free of rank `k`
away from the closed subscheme cut out by `Scheme.fittingIdealSheaf ℱ k`, then its strict
transform under the blowup of that subscheme is finite locally free of rank `k`. -/
@[stacks 0CZQ]
#check
  (AlgebraicGeometry.Scheme.fittingIdealSheaf.strictTransformModule_isFiniteLocallyFreeOfRank :
    ∀ {S S' : Scheme.{u}} (b : S' ⟶ S) (ℱ : S.Modules)
      [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (k : ℕ)
      [IsBlowup b (Scheme.fittingIdealSheaf ℱ k)]
      [SheafOfModules.IsFiniteLocallyFreeOfRank k
        ((Scheme.Modules.pullback (Scheme.fittingOpenComplement ℱ k).ι).obj ℱ)],
      SheafOfModules.IsFiniteLocallyFreeOfRank k
        (strictTransformModule b ((Scheme.fittingIdealSheaf ℱ k).comap b) (𝟙 S) ℱ))
