/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.InternalHom

open AlgebraicGeometry

universe u

/- Lemma 31.11.12: Let `X` be an integral scheme and let `ℱ` and `𝒢` be quasicoherent
`𝒪_X`-modules. If `𝒢` is torsion-free and `ℱ` is of finite presentation, then
`internalHom ℱ 𝒢` is torsion-free. -/
@[stacks 0AXZ] #check
  (AlgebraicGeometry.Scheme.Modules.isTorsionFree_internalHom :
    ∀ {X : Scheme.{u}} [IsIntegral X] (ℱ 𝒢 : X.Modules)
      [ℱ.IsFinitePresentation] [𝒢.IsQuasicoherent]
      [AlgebraicGeometry.Scheme.Modules.IsTorsionFree 𝒢],
      AlgebraicGeometry.Scheme.Modules.IsTorsionFree
        (AlgebraicGeometry.Scheme.Modules.internalHom ℱ 𝒢))
