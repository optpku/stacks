module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Finiteness
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Polynomial
public import ReasLib.RingTheory.Polynomial.EventualOrder
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degrees of Hilbert--Samuel Polynomials

@stack 00K9
@stack 00KA
@stack 00KQ

The degree of an eventual Hilbert--Samuel polynomial is independent of the
chosen ideal of definition.  Statements use arbitrary polynomial
representatives, so they do not depend on a chosen-polynomial owner.
-/

@[expose] public section

universe u v w

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

section Representative

variable [hR : IsNoetherianRing R] [hM : Module.Finite R M]
include hR hM

/-- The degrees of eventual `χ`-polynomial representatives are independent
of the ideal of definition. -/
@[stacks 00K9 "chi polynomial degree independence"]
theorem chiPolynomial_degree_eq {I I' : Ideal R}
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition)
    {P P' : Polynomial ℚ}
    (hP : P.EventuallyEqNat (fun n ↦ ((I.hilbertSamuelChi M n).toNat : ℚ)))
    (hP' : P'.EventuallyEqNat (fun n ↦ ((I'.hilbertSamuelChi M n).toNat : ℚ))) :
    P.degree = P'.degree := sorry

/-- The degrees of eventual `φ`-polynomial representatives are independent
of the ideal of definition. -/
@[stacks 00K9 "phi polynomial degree independence"]
theorem phiPolynomial_degree_eq {I I' : Ideal R}
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition)
    {P P' : Polynomial ℚ}
    (hP : P.EventuallyEqNat (fun n ↦ ((I.hilbertSamuelPhi M n).toNat : ℚ)))
    (hP' : P'.EventuallyEqNat (fun n ↦ ((I'.hilbertSamuelPhi M n).toNat : ℚ))) :
    P.degree = P'.degree := sorry

end Representative

/-! ### The canonical degree invariant

`degree` is deliberately owned by the Hilbert--Samuel namespace.  It is the
degree of the canonical maximal-ideal `χ` polynomial, while the preceding
theorems allow callers to work with any ideal-of-definition representative. -/

section Definition

variable (R : Type u) (M : Type v)
variable [CommRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M]

/-- The degree of the selected maximal-ideal Hilbert--Samuel `χ`-polynomial.
Under the usual Noetherian finite-module hypotheses, this is the ordinary
Hilbert--Samuel degree.  Outside that domain it is the total extension induced
by `chiPolynomial`, which uses the zero polynomial when no eventual
representative exists. -/
@[stacks 00KA "Hilbert-Samuel degree invariant"]
noncomputable def degree : WithBot ℕ :=
  (chiPolynomial (IsLocalRing.maximalIdeal R) M).degree

end Definition

section Canonical

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M]

variable [hR : IsNoetherianRing R] [hM : Module.Finite R M]
include hR hM

/-- The canonical degree agrees with any eventual `χ`-polynomial attached to
an ideal of definition. -/
@[stacks 00KA "degree of an ideal-of-definition chi polynomial"]
theorem degree_eq_of_isIdealOfDefinition {I : Ideal R}
    (hI : I.IsIdealOfDefinition) {P : Polynomial ℚ}
    (hP : P.EventuallyEqNat (fun n ↦ ((I.hilbertSamuelChi M n).toNat : ℚ))) :
    degree R M = P.degree := sorry

/-- The Hilbert--Samuel degree is invariant under a linear equivalence.  The
finite-module hypothesis on the target is derived from the equivalence, so it
is not an extra consumer argument. -/
@[stacks 00KA "degree invariance under linear equivalence"]
theorem degree_eq_of_linearEquiv
    {N : Type w} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    degree R M = degree R N := sorry

/-- Passing to a quotient module cannot increase the Hilbert--Samuel degree. -/
@[stacks 00KQ "quotient module Hilbert-Samuel degree bound"]
theorem degree_quotient_le (N : Submodule R M) :
    degree R (M ⧸ N) ≤ degree R M := sorry

end Canonical

section Basic

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Any eventual maximal-ideal `χ`-polynomial has the canonical degree.  Its
eventual-representation hypothesis is the only existence input required. -/
@[stacks 00KA "degree of an eventual chi polynomial"]
theorem degree_eq_of_eventuallyEq {P : Polynomial ℚ}
    (hP : P.EventuallyEqNat (fun n ↦
      ((Ideal.hilbertSamuelChi (IsLocalRing.maximalIdeal R) M n).toNat : ℚ))) :
    degree R M = P.degree := sorry

/-- The degree of a subsingleton module is bottom, independently of finiteness
or Noetherian hypotheses. -/
@[stacks 00KA "degree of a subsingleton module"]
theorem degree_eq_bot [Subsingleton M] :
    degree R M = (⊥ : WithBot ℕ) := sorry

end Basic

section RingQuotient

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable [hR : IsNoetherianRing R]
include hR

/-- Passing from a local Noetherian ring to an ideal quotient cannot increase
the ambient Hilbert--Samuel degree. -/
@[stacks 00KQ "ideal quotient Hilbert-Samuel degree bound"]
theorem degree_quotient_le_self (I : Ideal R) :
    degree R (R ⧸ I) ≤ degree R R := sorry

end RingQuotient

end Ideal.HilbertSamuel
