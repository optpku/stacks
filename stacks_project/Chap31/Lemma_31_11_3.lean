/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Affine

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 31.11.3: A quasicoherent module sheaf on an integral scheme is torsion free exactly
when its sections on every affine open are torsion free over the corresponding ring of
functions. -/
@[stacks 0AXS] #check
  (AlgebraicGeometry.Scheme.Modules.isTorsionFree_iff_affineOpen :
    ∀ {X : Scheme.{u}} [IsIntegral X] (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      AlgebraicGeometry.Scheme.Modules.IsTorsionFree ℱ ↔
        ∀ U : X.Opens, IsAffineOpen U → Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U)))
