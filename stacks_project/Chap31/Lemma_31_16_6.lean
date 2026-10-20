/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Complement.Existence

open TopologicalSpace

universe u

/- Lemma 31.16.6: let `X` be a Noetherian separated scheme and let `U ⊆ X` be a dense affine
open. If every local ring `𝒪_{X, x}` for `x ∈ X \ U` is a unique factorization domain, then
`U` is the open complement of an effective Cartier divisor on `X`. -/
@[stacks 0BCW] #check
  (AlgebraicGeometry.Scheme.OpenComplement.exists_effectiveCartierDivisor_of_isSeparated :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated]
      {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → Dense (U : Set X) →
      (∀ x : X, x ∉ (U : Set X) → UniqueFactorizationMonoid (X.presheaf.stalk x)) →
      ∃ D : X.IdealSheafData,
        AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι ∧ U = D.openComplement)
