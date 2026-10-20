/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Approximation
import StacksCheckRecall

/-!
# Lemma 31.15.8

Effective Cartier divisor approximations away from codimension two.

@stack 0AGB
-/

@[expose] public section

open Set TopologicalSpace

universe u v

/- Lemma 31.15.8 (1): a closed subscheme of a Noetherian scheme that is covered by integral
effective Cartier divisors away from codimension `2` admits a finitely supported weighted
effective-Cartier approximation. -/
@[stacks 0AGB] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.EffectiveCartierDivisorApproximation.exists_weightedSum :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian X] {ι : Type v}
      (Z : X.IdealSheafData) (D : ι → X.IdealSheafData)
      (hCartier : ∀ i, AlgebraicGeometry.IsEffectiveCartierDivisor (D i).subschemeι)
      (hIntegral : ∀ i, AlgebraicGeometry.IsIntegral (D i).subscheme)
      (Z' : Set X) (hZ'closed : IsClosed Z')
      (hZ'codim :
        AlgebraicGeometry.Scheme.IdealSheafData.irreducibleComponentsCodimAtLeast 2 Z')
      (hcover : (Z.support : Set X) ⊆ Z' ∪ ⋃ i, ((D i).support : Set X)),
      ∃ a : ι →₀ ℕ,
        AlgebraicGeometry.Scheme.IdealSheafData.EffectiveCartierDivisorApproximation
          (AlgebraicGeometry.Scheme.IdealSheafData.effectiveCartierDivisorWeightedSum a D) Z)

/- Lemma 31.15.8 (2): for a nowhere-dense closed subscheme of a Noetherian scheme, unique
factorization of the ambient stalks along its support supplies the integral effective Cartier
divisors and the closed codimension-two residual locus required above. -/
@[stacks 0AGB] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.EffectiveCartierDivisorApproximation.exists_cover_of_stalks_uniqueFactorizationMonoid :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
      (Z : X.IdealSheafData) (hnowhere : IsNowhereDense (Z.support : Set X))
      (hUFD : ∀ x : X, x ∈ Z.support → UniqueFactorizationMonoid (X.presheaf.stalk x)),
      ∃ (ι : Type u) (D : ι → X.IdealSheafData) (Z' : Set X),
        (∀ i, AlgebraicGeometry.IsEffectiveCartierDivisor (D i).subschemeι) ∧
          (∀ i, AlgebraicGeometry.IsIntegral (D i).subscheme) ∧
            IsClosed Z' ∧
              AlgebraicGeometry.Scheme.IdealSheafData.irreducibleComponentsCodimAtLeast 2 Z' ∧
                (Z.support : Set X) ⊆ Z' ∪ ⋃ i, ((D i).support : Set X))

/- Lemma 31.15.8 (3): for a nowhere-dense closed subscheme of a regular Noetherian scheme, an
integral effective Cartier family and a closed codimension-two residual locus satisfying the
required cover exist. -/
@[stacks 0AGB] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.EffectiveCartierDivisorApproximation.exists_cover_of_regular :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
      [AlgebraicGeometry.Scheme.Regular X] (Z : X.IdealSheafData)
      (hnowhere : IsNowhereDense (Z.support : Set X)),
      ∃ (ι : Type u) (D : ι → X.IdealSheafData) (Z' : Set X),
        (∀ i, AlgebraicGeometry.IsEffectiveCartierDivisor (D i).subschemeι) ∧
          (∀ i, AlgebraicGeometry.IsIntegral (D i).subscheme) ∧
            IsClosed Z' ∧
              AlgebraicGeometry.Scheme.IdealSheafData.irreducibleComponentsCodimAtLeast 2 Z' ∧
                (Z.support : Set X) ⊆ Z' ∪ ⋃ i, ((D i).support : Set X))
