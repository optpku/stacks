/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Flat

universe u

/- Lemma 31.11.5
Let `X` be an integral scheme. Any flat quasicoherent `𝒪_X`-module is torsion free.
-/
@[stacks 0AXU] #check
  (AlgebraicGeometry.Scheme.Modules.IsFlat.isTorsionFree :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent ℱ] [SheafOfModules.IsFlat ℱ],
      AlgebraicGeometry.Scheme.Modules.IsTorsionFree ℱ)
