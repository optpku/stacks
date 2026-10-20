module

public import Mathlib.Data.Finite.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Completion.PolynomialLocalization
import StacksCheckRecall

@[expose] public section

open IsLocalRing

universe u

/- 98.10.1.1: if a finite-variable polynomial map is surjective modulo the square
of the maximal ideal, its induced map from the completed localization is surjective. -/
@[stacks 07XC] #check (MvPolynomial.toCompleteLocal_surjective :
  ∀ {Λ σ R : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Finite σ]
    [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    (m' : Ideal (MvPolynomial σ Λ)) [m'.IsPrime]
    (ψ : MvPolynomial σ Λ →+* R)
    (h_comap : m' = (maximalIdeal R).comap ψ)
    (h_sq : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal R ^ 2)).comp ψ)),
    Function.Surjective (MvPolynomial.toCompleteLocal m' ψ h_comap))
