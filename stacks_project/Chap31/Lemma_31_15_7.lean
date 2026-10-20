/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.UniqueFactorization
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.15.7: let `X` be a locally Noetherian scheme and let `D ⊆ X` be an integral closed
subscheme. Assume that `D` has codimension `1` in `X`, expressed here by
`ringKrullDim (𝒪_{X, ξ}) = 1` at the image `ξ` of the generic point of `D`, and
assume that every local ring `𝒪_{X, x}` with `x ∈ D` is a unique factorization domain.
Then `D` is an effective Cartier divisor. -/
@[stacks 0AGA] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.isEffectiveCartierDivisor_of_uniqueFactorizationMonoid :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
        (D : X.IdealSheafData) [AlgebraicGeometry.IsIntegral D.subscheme]
        (hcodim : ringKrullDim
          (X.presheaf.stalk (D.subschemeι.base (genericPoint D.subscheme))) = 1)
        (hUFD : ∀ x : X, x ∈ D.support →
          UniqueFactorizationMonoid (X.presheaf.stalk x)),
      AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι)
