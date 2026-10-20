/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Stalk

universe u

/- Lemma 31.11.8: let `X` be an integral scheme and let `ℱ` be a quasicoherent `𝒪_X`-module.
Then `ℱ` is torsion free if and only if every stalk `ℱₓ` is torsion free over `𝒪_{X,x}`. -/
@[stacks 0AXW] #check
  (AlgebraicGeometry.Scheme.Modules.isTorsionFree_iff_stalkwise :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      AlgebraicGeometry.Scheme.Modules.IsTorsionFree ℱ ↔
        ∀ x : X, Module.IsTorsionFree (X.presheaf.stalk x)
          (AlgebraicGeometry.RingedSpace.stalkModuleCat ℱ x))
