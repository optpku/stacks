/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.Hilbert
public import ReasLib.RingTheory.Polynomial.Evaluation
public import ReasLib.RingTheory.Polynomial.Numerical.Representative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hilbert--Samuel Numerical Polynomials

The core theorem is stated for any ideal with Artinian quotient.  The familiar
Noetherian-local formulation for an ideal of definition is supplied as a thin
specialization for source texts and downstream applications.
-/

@[expose] public section

universe u v

/-! ### Canonical eventual polynomials

The reusable API lives below the Hilbert--Samuel namespace.  The module
argument remains explicit, while the construction is identified by the
invariant (`chiPolynomial` or `phiPolynomial`). -/

namespace Ideal.HilbertSamuel

section Generic

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The integer-tail `φ`-function of any Artinian quotient is represented by
an ordinary rational polynomial eventually. -/
@[stacks 00K8 "Artinian-quotient generalization of phi numerical polynomiality"]
theorem exists_phiPolynomial (I : Ideal R) [IsArtinianRing (R ⧸ I)] :
    ∃ P : Polynomial ℚ,
      P.EventuallyEqNat (fun n ↦ ((Ideal.hilbertSamuelPhi I M n).toNat : ℚ)) := sorry

/-- The integer-tail `χ`-function of any Artinian quotient is represented by
an ordinary rational polynomial eventually. -/
@[stacks 00K8 "Artinian-quotient generalization of chi numerical polynomiality"]
theorem exists_chiPolynomial (I : Ideal R) [IsArtinianRing (R ⧸ I)] :
    ∃ P : Polynomial ℚ,
      P.EventuallyEqNat (fun n ↦ ((Ideal.hilbertSamuelChi I M n).toNat : ℚ)) := sorry

/-- Short namespace-facing form of the generic `φ` numerical-polynomial API. -/
@[stacks 00K8 "Artinian-quotient phi numerical polynomial"]
theorem phi_isNumericalPolynomial (I : Ideal R) [IsArtinianRing (R ⧸ I)] :
    IsNumericalPolynomial
      (fun n : ℤ ↦ ((Ideal.hilbertSamuelPhi I M n.toNat).toNat : ℚ)) := sorry

/-- Short namespace-facing form of the generic `χ` numerical-polynomial API. -/
@[stacks 00K8 "Artinian-quotient chi numerical polynomial"]
theorem chi_isNumericalPolynomial (I : Ideal R) [IsArtinianRing (R ⧸ I)] :
    IsNumericalPolynomial
      (fun n : ℤ ↦ ((Ideal.hilbertSamuelChi I M n.toNat).toNat : ℚ)) := sorry

end Generic

section OfDefinition

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The integer-tail `φ`-function for an ideal of definition is a numerical polynomial. -/
@[stacks 00K8 "ideal-of-definition phi numerical polynomial"]
theorem phi_isNumericalPolynomial_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    IsNumericalPolynomial
      (fun n : ℤ ↦ ((Ideal.hilbertSamuelPhi I M n.toNat).toNat : ℚ)) := sorry

/-- The integer-tail `χ`-function for an ideal of definition is a numerical polynomial. -/
@[stacks 00K8 "ideal-of-definition chi numerical polynomial"]
theorem chi_isNumericalPolynomial_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    IsNumericalPolynomial
      (fun n : ℤ ↦ ((Ideal.hilbertSamuelChi I M n.toNat).toNat : ℚ)) := sorry

/-- An ideal-of-definition `φ`-function has an eventual rational polynomial representative. -/
@[stacks 09CA "ideal-of-definition phi polynomial existence"]
theorem exists_phiPolynomial_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    ∃ P : Polynomial ℚ,
      P.EventuallyEqNat (fun n ↦ ((Ideal.hilbertSamuelPhi I M n).toNat : ℚ)) := sorry

/-- An ideal-of-definition `χ`-function has an eventual rational polynomial representative. -/
@[stacks 00KA "ideal-of-definition chi polynomial existence"]
theorem exists_chiPolynomial_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    ∃ P : Polynomial ℚ,
      P.EventuallyEqNat (fun n ↦ ((Ideal.hilbertSamuelChi I M n).toNat : ℚ)) := sorry

end OfDefinition

section Canonical

variable {R : Type u} [CommRing R]
variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/-- A totalized candidate for the rational polynomial representing the Hilbert--Samuel
`φ`-function of `I`.  Read it as a genuine representative only through
`phiPolynomial_eventuallyEqNat_iff` or a specification theorem. -/
@[stacks 09CA "Hilbert-Samuel phi polynomial"]
noncomputable def phiPolynomial : Polynomial ℚ :=
  Polynomial.eventualRepresentative
    (fun n ↦ ((Ideal.hilbertSamuelPhi I M n).toNat : ℚ))

/-- A totalized candidate for the rational polynomial representing the Hilbert--Samuel
`χ`-function of `I`.  Read it as a genuine representative only through
`chiPolynomial_eventuallyEqNat_iff` or a specification theorem. -/
@[stacks 00KA "Hilbert-Samuel chi polynomial"]
noncomputable def chiPolynomial : Polynomial ℚ :=
  Polynomial.eventualRepresentative
    (fun n ↦ ((Ideal.hilbertSamuelChi I M n).toNat : ℚ))

/-- The totalized `φ` candidate is an eventual representative exactly when such a representative
exists. -/
@[stacks 09CA "Hilbert-Samuel phi polynomial existence characterization"]
theorem phiPolynomial_eventuallyEqNat_iff :
    (phiPolynomial I M).EventuallyEqNat
        (fun n ↦ ((Ideal.hilbertSamuelPhi I M n).toNat : ℚ)) ↔
      ∃ P : Polynomial ℚ,
        P.EventuallyEqNat (fun n ↦ ((Ideal.hilbertSamuelPhi I M n).toNat : ℚ)) := sorry

/-- The totalized `χ` candidate is an eventual representative exactly when such a representative
exists. -/
@[stacks 00KA "Hilbert-Samuel chi polynomial existence characterization"]
theorem chiPolynomial_eventuallyEqNat_iff :
    (chiPolynomial I M).EventuallyEqNat
        (fun n ↦ ((Ideal.hilbertSamuelChi I M n).toNat : ℚ)) ↔
      ∃ P : Polynomial ℚ,
        P.EventuallyEqNat (fun n ↦ ((Ideal.hilbertSamuelChi I M n).toNat : ℚ)) := sorry

variable [IsNoetherianRing R] [Module.Finite R M] [IsArtinianRing (R ⧸ I)]

/-- There is a unique eventual rational polynomial representing the `φ`-function of `I`. -/
@[stacks 09CA "Hilbert-Samuel phi polynomial uniqueness"]
theorem existsUnique_phiPolynomial :
    ∃! P : Polynomial ℚ,
      P.EventuallyEqNat (fun n ↦ ((Ideal.hilbertSamuelPhi I M n).toNat : ℚ)) := sorry

/-- There is a unique eventual rational polynomial representing the `χ`-function of `I`. -/
@[stacks 00KA "Hilbert-Samuel chi polynomial uniqueness"]
theorem existsUnique_chiPolynomial :
    ∃! P : Polynomial ℚ,
      P.EventuallyEqNat (fun n ↦ ((Ideal.hilbertSamuelChi I M n).toNat : ℚ)) := sorry

/-- The selected `φ`-polynomial agrees with the Hilbert--Samuel `φ`-function eventually. -/
@[stacks 09CA "Hilbert-Samuel phi polynomial specification"]
theorem phiPolynomial_spec :
    (phiPolynomial I M).EventuallyEqNat
      (fun n ↦ ((Ideal.hilbertSamuelPhi I M n).toNat : ℚ)) := sorry

/-- The selected `χ`-polynomial agrees with the Hilbert--Samuel `χ`-function eventually. -/
@[stacks 00KA "Hilbert-Samuel chi polynomial specification"]
theorem chiPolynomial_spec :
    (chiPolynomial I M).EventuallyEqNat
      (fun n ↦ ((Ideal.hilbertSamuelChi I M n).toNat : ℚ)) := sorry

/-- Any eventual representative of the `φ`-function of `I` is `phiPolynomial I M`. -/
@[stacks 09CA "Hilbert-Samuel phi polynomial uniqueness bridge"]
theorem eq_phiPolynomial {P : Polynomial ℚ}
    (hP : P.EventuallyEqNat (fun n ↦ ((Ideal.hilbertSamuelPhi I M n).toNat : ℚ))) :
    P = phiPolynomial I M := sorry

/-- Any eventual representative of the `χ`-function of `I` is `chiPolynomial I M`. -/
@[stacks 00KA "Hilbert-Samuel chi polynomial uniqueness bridge"]
theorem eq_chiPolynomial {P : Polynomial ℚ}
    (hP : P.EventuallyEqNat (fun n ↦ ((Ideal.hilbertSamuelChi I M n).toNat : ℚ))) :
    P = chiPolynomial I M := sorry

/-- A polynomial eventually represents the `φ`-function of `I` exactly when it equals the selected
representative. -/
@[stacks 09CA "Hilbert-Samuel phi polynomial characterization"]
theorem eventuallyEq_phi_iff_eq_phiPolynomial (P : Polynomial ℚ) :
    P.EventuallyEqNat (fun n ↦ ((Ideal.hilbertSamuelPhi I M n).toNat : ℚ)) ↔
      P = phiPolynomial I M := sorry

/-- A polynomial eventually represents the `χ`-function of `I` exactly when it equals the selected
representative. -/
@[stacks 00KA "Hilbert-Samuel chi polynomial characterization"]
theorem eventuallyEq_chi_iff_eq_chiPolynomial (P : Polynomial ℚ) :
    P.EventuallyEqNat (fun n ↦ ((Ideal.hilbertSamuelChi I M n).toNat : ℚ)) ↔
      P = chiPolynomial I M := sorry

end Canonical

section OfDefinitionSpec

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The selected `φ`-polynomial represents the `φ`-function of an ideal of definition,
without requiring callers to install the Artinian quotient instance. -/
@[stacks 09CA "ideal-of-definition phi polynomial specification"]
theorem phiPolynomial_spec_of_isIdealOfDefinition (hI : I.IsIdealOfDefinition) :
    (phiPolynomial I M).EventuallyEqNat
      (fun n ↦ ((Ideal.hilbertSamuelPhi I M n).toNat : ℚ)) := sorry

/-- The selected `χ`-polynomial represents the `χ`-function of an ideal of definition,
without requiring callers to install the Artinian quotient instance. -/
@[stacks 00KA "ideal-of-definition chi polynomial specification"]
theorem chiPolynomial_spec_of_isIdealOfDefinition (hI : I.IsIdealOfDefinition) :
    (chiPolynomial I M).EventuallyEqNat
      (fun n ↦ ((Ideal.hilbertSamuelChi I M n).toNat : ℚ)) := sorry

/-- The selected maximal-ideal `φ`-polynomial represents the local Hilbert--Samuel
`φ`-function eventually. -/
@[stacks 09CA "maximal-ideal phi polynomial specification"]
theorem phiPolynomial_spec_maximalIdeal :
    (phiPolynomial (IsLocalRing.maximalIdeal R) M).EventuallyEqNat
      (fun n ↦ ((Ideal.hilbertSamuelPhi (IsLocalRing.maximalIdeal R) M n).toNat : ℚ)) := sorry

/-- The selected maximal-ideal `χ`-polynomial represents the local Hilbert--Samuel
`χ`-function eventually. -/
@[stacks 00KA "maximal-ideal chi polynomial specification"]
theorem chiPolynomial_spec_maximalIdeal :
    (chiPolynomial (IsLocalRing.maximalIdeal R) M).EventuallyEqNat
      (fun n ↦ ((Ideal.hilbertSamuelChi (IsLocalRing.maximalIdeal R) M n).toNat : ℚ)) := sorry

end OfDefinitionSpec

end Ideal.HilbertSamuel
