/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Approximation

/-!
# Decomposition of effective Cartier divisors

This file gives finite weighted decompositions of effective Cartier divisors into integral
effective Cartier divisors, together with criteria ensuring the existence of a covering family.
-/

@[expose] public section

open AlgebraicGeometry
open Set TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.IdealSheafData.EffectiveCartierDivisorDecomposition

variable {X : Scheme.{u}}
variable {ι : Type v}

/-- An effective Cartier divisor on a Noetherian scheme whose support is covered by supports of
integral effective Cartier divisors is a finite weighted sum of those divisors. -/
theorem exists_eq_weightedSum_of_support_subset_iUnion
    [IsNoetherian X] (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (Dᵢ : ι → X.IdealSheafData)
    (hCartier : ∀ i, AlgebraicGeometry.IsEffectiveCartierDivisor (Dᵢ i).subschemeι)
    (hIntegral : ∀ i, IsIntegral (Dᵢ i).subscheme)
    (hcover : (D.support : Set X) ⊆ ⋃ i, ((Dᵢ i).support : Set X)) :
    ∃ a : ι →₀ ℕ, D = effectiveCartierDivisorWeightedSum a Dᵢ := sorry

/-- An effective Cartier divisor on a Noetherian scheme is covered by integral effective Cartier
divisors when every ambient stalk along its support is a unique factorization monoid. -/
theorem exists_cover_of_stalks_uniqueFactorizationMonoid
    [IsNoetherian X] (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (hUFD : ∀ x : X, x ∈ D.support → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ (ι : Type u) (Dᵢ : ι → X.IdealSheafData),
      (∀ i, AlgebraicGeometry.IsEffectiveCartierDivisor (Dᵢ i).subschemeι) ∧
        (∀ i, IsIntegral (Dᵢ i).subscheme) ∧
          (D.support : Set X) ⊆ ⋃ i, ((Dᵢ i).support : Set X) := sorry

/-- An effective Cartier divisor on a regular Noetherian scheme is covered by integral effective
Cartier divisors. -/
theorem exists_cover_of_regular
    [IsNoetherian X] [Regular X] (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι] :
    ∃ (ι : Type u) (Dᵢ : ι → X.IdealSheafData),
      (∀ i, AlgebraicGeometry.IsEffectiveCartierDivisor (Dᵢ i).subschemeι) ∧
        (∀ i, IsIntegral (Dᵢ i).subscheme) ∧
          (D.support : Set X) ⊆ ⋃ i, ((Dᵢ i).support : Set X) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData.EffectiveCartierDivisorDecomposition
