/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Pushforward
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 31.6.2: Let `f : X ⟶ S` be an affine morphism of schemes and let `ℱ` be a
quasicoherent `𝒪_X`-module. If `X` is locally Noetherian, then the image of the associated points
of `ℱ`, the associated and weakly associated points of `f_* ℱ`, and the image of the weakly
associated points of `ℱ` are all equal. -/
@[stacks 05EY] #check
  (AlgebraicGeometry.Scheme.Modules.AffinePushforward.associatedPoints_weakAss_chain :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [IsLocallyNoetherian X],
      List.IsChain (· = ·)
        [f.base '' ℱ.associatedPoints,
          ((Scheme.Modules.pushforward f).obj ℱ).associatedPoints,
          ((Scheme.Modules.pushforward f).obj ℱ).weakAss,
          f.base '' ℱ.weakAss])
