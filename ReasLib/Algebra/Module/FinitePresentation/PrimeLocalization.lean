module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak

/-!
# Finite presentation detected by prime localizations

This leaf owns the finite family of prime localizations which detects equality, together with
the flat finite-presentation descent criteria for polynomial modules and finite-type algebras.

@stack 053A
@stack 053B
@stack 05GS
-/

@[expose] public section

open scoped TensorProduct

-- Local instance justification (instance diamond): use the polynomial right-factor action in
-- the iterated tensor product occurring in the localized module statement.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

namespace PrimeLocalization

/-- A finite family of prime localizations of `R` detects equality when the diagonal map from
`R` to their dependent product is injective. -/
@[stacks 05GS "prime localizations detecting equality"]
def DetectsEquality (R : Type u) [CommRing R] : Prop :=
  ∃ s : Finset (PrimeSpectrum R),
    Function.Injective
      (fun r : R ↦ fun p : s ↦ algebraMap R (Localization.AtPrime p.1.asIdeal) r)

namespace DetectsEquality

/-- Remark 15.25.5 (1): a local ring has a finite family of prime localizations which detects
equality. -/
@[stacks 05GS "Remark 15.25.5 (1)"]
theorem ofIsLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    PrimeLocalization.DetectsEquality R := sorry

/-- Remark 15.25.5 (2): a Noetherian ring has a finite family of prime localizations which
detects equality. -/
@[stacks 05GS "Remark 15.25.5 (2)"]
theorem ofIsNoetherianRing (R : Type u) [CommRing R] [IsNoetherianRing R] :
    PrimeLocalization.DetectsEquality R := sorry

/-- Remark 15.25.5 (3): a domain has a finite family of prime localizations which detects
equality. -/
@[stacks 05GS "Remark 15.25.5 (3)"]
theorem ofIsDomain (R : Type u) [CommRing R] [IsDomain R] :
    PrimeLocalization.DetectsEquality R := sorry

/-- Remark 15.25.5 (4): a reduced ring with finitely many minimal primes has a finite family of
prime localizations which detects equality. -/
@[stacks 05GS "Remark 15.25.5 (4)"]
theorem ofIsReducedOfFiniteMinimalPrimes
    (R : Type u) [CommRing R] [IsReduced R] (hfinite : (minimalPrimes R).Finite) :
    PrimeLocalization.DetectsEquality R := sorry

/-- Remark 15.25.5 (5): a ring with finitely many weakly associated primes has a finite family
of prime localizations which detects equality. -/
@[stacks 05GS "Remark 15.25.5 (5)"]
theorem ofFiniteWeaklyAssociatedPrimes
    (R : Type u) [CommRing R] (hfinite : (weaklyAssociatedPrimes R R).Finite) :
    PrimeLocalization.DetectsEquality R := sorry

end DetectsEquality

end PrimeLocalization

namespace Module.FinitePresentation

/-- Lemma 15.25.1: a finite module over a finite-variable polynomial ring, flat over the base,
is finitely presented when all of its prime-local base changes are finitely presented and a
finite family of base-prime localizations detects equality. -/
@[stacks 053A "Lemma 15.25.1"]
theorem ofFlatPrimeLocalizations
    {R : Type u} [CommRing R] (n : ℕ)
    {M : Type w} [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M] [Module R M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    [Module.Finite (MvPolynomial (Fin n) R) M] [Module.Flat R M]
    (hdetect : PrimeLocalization.DetectsEquality R)
    (hloc :
      ∀ p : PrimeSpectrum R,
        Module.FinitePresentation
          ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
          (((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ⊗[
            MvPolynomial (Fin n) R] M)) :
    Module.FinitePresentation (MvPolynomial (Fin n) R) M := sorry

end Module.FinitePresentation

namespace Algebra.FinitePresentation

/-- Lemma 15.25.2: a flat finite-type algebra is finitely presented when all prime-local base
changes are finitely presented and a finite family of base-prime localizations detects equality. -/
@[stacks 053B "Lemma 15.25.2"]
theorem ofFlatPrimeLocalizations
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Module.Flat R S]
    (hdetect : PrimeLocalization.DetectsEquality R)
    (hloc :
      ∀ p : PrimeSpectrum R,
        Algebra.FinitePresentation (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] S)) :
    Algebra.FinitePresentation R S := sorry

end Algebra.FinitePresentation
