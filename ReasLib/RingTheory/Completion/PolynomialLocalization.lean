/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.AdicCompletion.AtPrime
public import ReasLib.RingTheory.AdicCompletion.LocalMap
public import ReasLib.RingTheory.Completion.LocalRing

/-!
# Completed local maps from polynomial localizations

A polynomial map `ψ : MvPolynomial σ Λ →+* R` into a complete local ring, with
`m' = (maximalIdeal R).comap ψ`, induces a local map on the localization at `m'`
and then a map of completed local rings
`PrimeSpectrum.CompletedLocalRing ⟨m', inferInstance⟩ →+* R`.
-/

@[expose] public section

open IsLocalRing

noncomputable section

universe u

namespace MvPolynomial

/-- The localization of a polynomial ring at a prime ideal admits the induced map
  to a local target when the prime is the comap of the target's maximal ideal. -/
def liftToLocalized {Λ σ R : Type u} [CommRing Λ] [CommRing R] [IsLocalRing R]
    (m' : Ideal (MvPolynomial σ Λ)) [m'.IsPrime] (ψ : MvPolynomial σ Λ →+* R)
    (h_comap : m' = (maximalIdeal R).comap ψ) :
    Localization.AtPrime m' →+* R :=
  IsLocalization.lift (M := m'.primeCompl) (g := ψ) fun y ↦
    notMem_maximalIdeal.mp (h_comap ▸ (y.property : y.val ∉ m'))

/-- The induced localization map is local. -/
instance isLocalHom_liftToLocalized {Λ σ R : Type u} [CommRing Λ] [CommRing R]
    [IsLocalRing R] {m' : Ideal (MvPolynomial σ Λ)} [m'.IsPrime]
    {ψ : MvPolynomial σ Λ →+* R} {h_comap : m' = (maximalIdeal R).comap ψ} :
    IsLocalHom (liftToLocalized m' ψ h_comap) := sorry

/-- The completed local ring map induced by a polynomial homomorphism and a compatible prime. -/
def toCompleteLocal {Λ σ R : Type u} [CommRing Λ] [CommRing R]
    [IsCompleteLocalRing R] (m' : Ideal (MvPolynomial σ Λ)) [m'.IsPrime]
    (ψ : MvPolynomial σ Λ →+* R) (h_comap : m' = (maximalIdeal R).comap ψ) :
    PrimeSpectrum.CompletedLocalRing ⟨m', inferInstance⟩ →+* R :=
  (AdicCompletion.ofAlgEquiv (maximalIdeal R)).symm.toRingHom.comp
    (AdicCompletion.mapLocal (liftToLocalized m' ψ h_comap))

/-- The completed local map is local. -/
instance isLocalHom_toCompleteLocal {Λ σ R : Type u} [CommRing Λ] [CommRing R]
    [IsCompleteLocalRing R] {m' : Ideal (MvPolynomial σ Λ)} [m'.IsPrime]
    {ψ : MvPolynomial σ Λ →+* R} {h_comap : m' = (maximalIdeal R).comap ψ} :
    IsLocalHom (toCompleteLocal m' ψ h_comap) := sorry

/-- The completed local map restricts to the original polynomial homomorphism. -/
theorem toCompleteLocal_comp {Λ σ R : Type u} [CommRing Λ] [CommRing R]
    [IsCompleteLocalRing R] (m' : Ideal (MvPolynomial σ Λ)) [m'.IsPrime]
    (ψ : MvPolynomial σ Λ →+* R) (h_comap : m' = (maximalIdeal R).comap ψ) :
    (toCompleteLocal m' ψ h_comap).comp
      (algebraMap (MvPolynomial σ Λ)
        (PrimeSpectrum.CompletedLocalRing ⟨m', inferInstance⟩)) = ψ := sorry

/-- Under the finite-variable Noetherian hypotheses and square-quotient surjectivity,
  the completed local map is surjective. -/
theorem toCompleteLocal_surjective {Λ σ R : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Finite σ] [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    (m' : Ideal (MvPolynomial σ Λ)) [m'.IsPrime] (ψ : MvPolynomial σ Λ →+* R)
    (h_comap : m' = (maximalIdeal R).comap ψ)
    (h_sq : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal R ^ 2)).comp ψ)) :
    Function.Surjective (toCompleteLocal m' ψ h_comap) := sorry

end MvPolynomial
