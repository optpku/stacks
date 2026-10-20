/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Determinant.EffectiveCartier
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 31.15.13 (1): the reflexive determinant of the left module is invertible. -/
@[stacks 0B3T] #check
  (AlgebraicGeometry.Scheme.Modules.ReflexiveDeterminant.left_isInvertible_of_exact_to_effectiveCartierDivisor_pushforward :
    ∀ {X : Scheme.{u}} [IsIntegral X] [Scheme.Regular X]
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
      [SheafOfModules.IsFiniteLocallyFreeOfRank s 𝒢],
      Scheme.Modules.Invertible
        (Scheme.Modules.ReflexiveDeterminant.sheaf r ℱ))

/- Lemma 31.15.13 (2): the reflexive determinant of the middle module is invertible. -/
@[stacks 0B3T] #check
  (AlgebraicGeometry.Scheme.Modules.ReflexiveDeterminant.middle_isInvertible_of_exact_to_effectiveCartierDivisor_pushforward :
    ∀ {X : Scheme.{u}} [IsIntegral X] [Scheme.Regular X]
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
      [SheafOfModules.IsFiniteLocallyFreeOfRank s 𝒢],
      Scheme.Modules.Invertible
        (Scheme.Modules.ReflexiveDeterminant.sheaf r ℱ'))

/- Lemma 31.15.13 (3): the two reflexive determinants differ by a bounded nonnegative
tensor power of the effective Cartier divisor sheaf. -/
@[stacks 0B3T] #check
  (AlgebraicGeometry.Scheme.Modules.ReflexiveDeterminant.exists_iso_tensorPower_associatedSheaf :
    ∀ {X : Scheme.{u}} [IsIntegral X] [Scheme.Regular X]
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
      [SheafOfModules.IsFiniteLocallyFreeOfRank s 𝒢],
      ∃ k : ℕ, k ≤ Nat.min s r ∧
        Nonempty
          (Scheme.Modules.ReflexiveDeterminant.sheaf r ℱ' ≅
            tensorObj (Scheme.Modules.ReflexiveDeterminant.sheaf r ℱ)
              (Scheme.Modules.tensorPowerInt
                (Scheme.IdealSheafData.associatedSheaf D) (k : ℤ))))
