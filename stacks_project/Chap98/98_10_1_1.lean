module

public import Mathlib.Data.Finite.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap98.«98_10_1_1_Completion»

@[expose] public section

open IsLocalRing MvPolynomial

universe u

namespace MvPolynomial

/-- 98.10.1.1: after arranging a finite-variable polynomial lift `ψ` so that
`MvPolynomial σ Λ → R ⧸ maximalIdeal R ^ 2` is surjective, the induced map
`PrimeSpectrum.CompletedLocalRing ⟨m', inferInstance⟩ ⟶ R` is a surjection of
Noetherian complete local rings. -/
@[stacks 07XC]
theorem toCompleteLocal_surjective {Λ σ R : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Finite σ] [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    (m' : Ideal (MvPolynomial σ Λ)) [m'.IsPrime] (ψ : MvPolynomial σ Λ →+* R)
    (h_comap : m' = (maximalIdeal R).comap ψ)
    (h_sq : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal R ^ 2)).comp ψ)) :
    Function.Surjective (toCompleteLocal m' ψ h_comap) := sorry

end MvPolynomial
