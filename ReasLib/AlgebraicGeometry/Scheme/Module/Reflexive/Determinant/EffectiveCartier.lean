/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Determinant
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower

/-!
# Reflexive determinants and effective Cartier divisors

This file records how reflexive determinants change across an exact sequence whose
cokernel is a finite locally free module supported on an integral effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.ReflexiveDeterminant

variable {X : Scheme.{u}}

/-- In an exact sequence with finite locally free quotient on an integral effective Cartier
divisor, the reflexive determinant of the left module is invertible. -/
theorem left_isInvertible_of_exact_to_effectiveCartierDivisor_pushforward
    [IsIntegral X] [Scheme.Regular X]
    (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] [IsIntegral D.subscheme]
    (ℱ ℱ' : X.Modules) (𝒢 : D.subscheme.Modules)
    [ℱ.IsCoherent] [ℱ'.IsCoherent]
    (φ : ℱ ⟶ ℱ')
    (ψ : ℱ' ⟶ (Scheme.Modules.pushforward D.subschemeι).obj 𝒢)
    (hφψ : φ ≫ ψ = 0)
    (hExact : (ShortComplex.mk φ ψ hφψ).Exact) [Epi ψ]
    (r s : ℕ) (hdim : topologicalKrullDim X = 2)
    (U : X.Opens) (hU : Set.Nonempty (U : Set X))
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ.over U)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ'.over U)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s 𝒢] :
    Scheme.Modules.Invertible (sheaf r ℱ) := sorry

/-- In an exact sequence with finite locally free quotient on an integral effective Cartier
divisor, the reflexive determinant of the middle module is invertible. -/
theorem middle_isInvertible_of_exact_to_effectiveCartierDivisor_pushforward
    [IsIntegral X] [Scheme.Regular X]
    (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] [IsIntegral D.subscheme]
    (ℱ ℱ' : X.Modules) (𝒢 : D.subscheme.Modules)
    [ℱ.IsCoherent] [ℱ'.IsCoherent]
    (φ : ℱ ⟶ ℱ')
    (ψ : ℱ' ⟶ (Scheme.Modules.pushforward D.subschemeι).obj 𝒢)
    (hφψ : φ ≫ ψ = 0)
    (hExact : (ShortComplex.mk φ ψ hφψ).Exact) [Epi ψ]
    (r s : ℕ) (hdim : topologicalKrullDim X = 2)
    (U : X.Opens) (hU : Set.Nonempty (U : Set X))
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ.over U)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ'.over U)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s 𝒢] :
    Scheme.Modules.Invertible (sheaf r ℱ') := sorry

/-- In an exact sequence with rank-`s` quotient on an integral effective Cartier divisor,
the middle reflexive determinant is the left reflexive determinant tensored with the `k`-th
power of the divisor sheaf for some `k ≤ min s r`. -/
theorem exists_iso_tensorPower_associatedSheaf
    [IsIntegral X] [Scheme.Regular X]
    (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] [IsIntegral D.subscheme]
    (ℱ ℱ' : X.Modules) (𝒢 : D.subscheme.Modules)
    [ℱ.IsCoherent] [ℱ'.IsCoherent]
    (φ : ℱ ⟶ ℱ')
    (ψ : ℱ' ⟶ (Scheme.Modules.pushforward D.subschemeι).obj 𝒢)
    (hφψ : φ ≫ ψ = 0)
    (hExact : (ShortComplex.mk φ ψ hφψ).Exact) [Epi ψ]
    (r s : ℕ) (hdim : topologicalKrullDim X = 2)
    (U : X.Opens) (hU : Set.Nonempty (U : Set X))
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ.over U)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ'.over U)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s 𝒢] :
    ∃ k : ℕ, k ≤ Nat.min s r ∧
      Nonempty
        (sheaf r ℱ' ≅
          tensorObj (sheaf r ℱ)
            (Scheme.Modules.tensorPowerInt
              (Scheme.IdealSheafData.associatedSheaf D) (k : ℤ))) := sorry

end AlgebraicGeometry.Scheme.Modules.ReflexiveDeterminant
