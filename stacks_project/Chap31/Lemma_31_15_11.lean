/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Decomposition
import StacksCheckRecall

open AlgebraicGeometry
open Set TopologicalSpace

universe u v

/- Lemma 31.15.11 (1): let `X` be a Noetherian scheme and let `D ⊆ X` be an effective Cartier
divisor. If `D` is set-theoretically contained in the union of integral effective Cartier
divisors `Dᵢ`, then `D` is a finite weighted sum `∑ i, aᵢ Dᵢ`. -/
@[stacks 0BCP] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.EffectiveCartierDivisorDecomposition.exists_eq_weightedSum_of_support_subset_iUnion :
    ∀ {X : Scheme.{u}} {ι : Type v} [IsNoetherian X]
      (D : X.IdealSheafData) [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      (Dᵢ : ι → X.IdealSheafData)
      (hCartier : ∀ i, AlgebraicGeometry.IsEffectiveCartierDivisor (Dᵢ i).subschemeι)
      (hIntegral : ∀ i, IsIntegral (Dᵢ i).subscheme)
      (hcover : (D.support : Set X) ⊆ ⋃ i, ((Dᵢ i).support : Set X)),
      ∃ a : ι →₀ ℕ,
        D = AlgebraicGeometry.Scheme.IdealSheafData.effectiveCartierDivisorWeightedSum a Dᵢ)

/- Lemma 31.15.11 (2): the required covering family exists when every ambient local ring along
the support of the effective Cartier divisor is a unique factorization domain. -/
@[stacks 0BCP] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.EffectiveCartierDivisorDecomposition.exists_cover_of_stalks_uniqueFactorizationMonoid :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      (D : X.IdealSheafData) [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      (hUFD : ∀ x : X, x ∈ D.support → UniqueFactorizationMonoid (X.presheaf.stalk x)),
      ∃ (ι : Type u) (Dᵢ : ι → X.IdealSheafData),
        (∀ i, AlgebraicGeometry.IsEffectiveCartierDivisor (Dᵢ i).subschemeι) ∧
          (∀ i, IsIntegral (Dᵢ i).subscheme) ∧
            (D.support : Set X) ⊆ ⋃ i, ((Dᵢ i).support : Set X))

/- Lemma 31.15.11 (3): the required covering family exists when the Noetherian ambient scheme is
regular. -/
@[stacks 0BCP] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.EffectiveCartierDivisorDecomposition.exists_cover_of_regular :
    ∀ {X : Scheme.{u}} [IsNoetherian X] [Scheme.Regular X]
      (D : X.IdealSheafData) [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      ∃ (ι : Type u) (Dᵢ : ι → X.IdealSheafData),
        (∀ i, AlgebraicGeometry.IsEffectiveCartierDivisor (Dᵢ i).subschemeι) ∧
          (∀ i, IsIntegral (Dᵢ i).subscheme) ∧
            (D.support : Set X) ⊆ ⋃ i, ((Dᵢ i).support : Set X))
