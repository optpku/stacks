/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.FractionRing.Jacobson
import StacksCheckRecall

/-!
# Lemma 33.37.8

The finite-family Jacobson-radical denominator statement is the direct
`FractionRing.Jacobson.exists_nonzero_with_inv_mem_jacobson` API.
-/

open scoped TensorProduct

universe u v w

/- Lemma 33.37.8: a common nonzero denominator has inverse in every Jacobson radical. -/
@[stacks 09N5] #check
  (FractionRing.Jacobson.exists_nonzero_with_inv_mem_jacobson :
    ∀ {A : Type u} [CommRing A] [IsDomain A]
      {K : Type v} [Field K] [Algebra A K]
      {ι : Type w} {B : ι → Type w}
      [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
      [∀ i, Algebra (B i) K] [Finite ι],
      IsFractionRing A K →
      (∀ i, IsFractionRing (B i) K) →
      (∀ i, IsNoetherianRing (B i)) →
      (∀ i, Finite (MaximalSpectrum (B i))) →
      (∀ i, ringKrullDim (B i) = 1) →
      (∀ i,
        Function.Surjective
          ((Algebra.TensorProduct.productMap
              (IsScalarTower.toAlgHom ℤ A K)
              (IsScalarTower.toAlgHom ℤ (B i) K)) : A ⊗[ℤ] B i →ₐ[ℤ] K)) →
      ∃ x : A, x ≠ 0 ∧ ∀ i,
        ∃ y : Ring.jacobson (B i), algebraMap (B i) K y = (algebraMap A K x)⁻¹)
