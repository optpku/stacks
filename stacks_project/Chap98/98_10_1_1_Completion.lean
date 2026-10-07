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

/-- The induced local homomorphism `Localization.AtPrime m' →+* R` of a
polynomial map `ψ` with `m' = (maximalIdeal R).comap ψ`. -/
def liftToLocalized {Λ σ R : Type u} [CommRing Λ] [CommRing R] [IsLocalRing R]
    (m' : Ideal (MvPolynomial σ Λ)) [m'.IsPrime] (ψ : MvPolynomial σ Λ →+* R)
    (h_comap : m' = (maximalIdeal R).comap ψ) :
    Localization.AtPrime m' →+* R :=
  IsLocalization.lift (M := m'.primeCompl) (g := ψ) fun y ↦
    notMem_maximalIdeal.mp (h_comap ▸ (y.property : y.val ∉ m'))

/-- The polynomial localization lift is a local homomorphism. -/
instance isLocalHom_liftToLocalized {Λ σ R : Type u} [CommRing Λ] [CommRing R]
    [IsLocalRing R] {m' : Ideal (MvPolynomial σ Λ)} [m'.IsPrime]
    {ψ : MvPolynomial σ Λ →+* R} {h_comap : m' = (maximalIdeal R).comap ψ} :
    IsLocalHom (liftToLocalized m' ψ h_comap) := sorry

/-- The induced map on completed local rings
`PrimeSpectrum.CompletedLocalRing ⟨m', inferInstance⟩ →+* R` extending a
polynomial lift `ψ` along the maximal-adic completion. -/
def toCompleteLocal {Λ σ R : Type u} [CommRing Λ] [CommRing R]
    [IsCompleteLocalRing R] (m' : Ideal (MvPolynomial σ Λ)) [m'.IsPrime]
    (ψ : MvPolynomial σ Λ →+* R) (h_comap : m' = (maximalIdeal R).comap ψ) :
    PrimeSpectrum.CompletedLocalRing ⟨m', inferInstance⟩ →+* R :=
  (AdicCompletion.ofAlgEquiv (maximalIdeal R)).symm.toRingHom.comp
    (AdicCompletion.mapLocal (liftToLocalized m' ψ h_comap))

/-- The completed local map is a local homomorphism. -/
instance isLocalHom_toCompleteLocal {Λ σ R : Type u} [CommRing Λ] [CommRing R]
    [IsCompleteLocalRing R] {m' : Ideal (MvPolynomial σ Λ)} [m'.IsPrime]
    {ψ : MvPolynomial σ Λ →+* R} {h_comap : m' = (maximalIdeal R).comap ψ} :
    IsLocalHom (toCompleteLocal m' ψ h_comap) := sorry

/-- The completed local map extends the original polynomial homomorphism. -/
theorem toCompleteLocal_comp {Λ σ R : Type u} [CommRing Λ] [CommRing R]
    [IsCompleteLocalRing R] (m' : Ideal (MvPolynomial σ Λ)) [m'.IsPrime]
    (ψ : MvPolynomial σ Λ →+* R) (h_comap : m' = (maximalIdeal R).comap ψ) :
    (toCompleteLocal m' ψ h_comap).comp
      (algebraMap (MvPolynomial σ Λ)
        (PrimeSpectrum.CompletedLocalRing ⟨m', inferInstance⟩)) = ψ := sorry

end MvPolynomial
