/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Dimension
public import ReasLib.RingTheory.RegularLocalRing.Parameters
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hilbert--Samuel Multiplicity

This file defines Hilbert--Samuel multiplicity from the canonical
Hilbert--Samuel `χ`-polynomial and records its characterization in the support
dimension, together with the multiplicity-versus-colength bound for parameter
ideals.
-/

@[expose] public section

universe u v

namespace Ideal.HilbertSamuel

/-- The degree-`d` algebraic multiplicity is `d!` times the degree-`d` coefficient of the
canonical Hilbert--Samuel `χ`-polynomial. -/
noncomputable def multiplicityInDegree {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (d : ℕ) : ℚ :=
  (d.factorial : ℚ) * (chiPolynomial I M).coeff d

/-- Degree-`d` algebraic multiplicity in terms of the canonical Hilbert--Samuel polynomial
coefficient. -/
theorem multiplicityInDegree_def {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (d : ℕ) :
    multiplicityInDegree I M d =
      (d.factorial : ℚ) * (chiPolynomial I M).coeff d := sorry

/-- The algebraic multiplicity is the normalized leading coefficient of the canonical
Hilbert--Samuel `χ`-polynomial. -/
noncomputable def multiplicity {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : ℚ :=
  ((chiPolynomial I M).natDegree.factorial : ℚ) * (chiPolynomial I M).leadingCoeff

/-- Algebraic multiplicity in terms of the leading coefficient of the canonical
Hilbert--Samuel polynomial. -/
theorem multiplicity_def {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    multiplicity I M =
      ((chiPolynomial I M).natDegree.factorial : ℚ) *
        (chiPolynomial I M).leadingCoeff := sorry

section Local

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Degree-`d` algebraic multiplicity may be computed from any eventual polynomial
representative of the Hilbert--Samuel `χ`-function for an ideal of definition. -/
theorem multiplicityInDegree_eq_of_eventuallyEq (I : Ideal R)
    (hI : I.IsIdealOfDefinition) {P : Polynomial ℚ}
    (hP : P.EventuallyEqNat (fun n ↦ ((I.hilbertSamuelChi M n).toNat : ℚ))) (d : ℕ) :
    multiplicityInDegree I M d = (d.factorial : ℚ) * P.coeff d := sorry

/-- For an ideal of definition and `Module.supportDim R M ≤ d`, degree-`d` algebraic
multiplicity vanishes above the support dimension and is the normalized leading coefficient in
the top degree. -/
theorem multiplicityInDegree_spec (I : Ideal R) (hI : I.IsIdealOfDefinition) (d : ℕ)
    (hd : Module.supportDim R M ≤ d) :
    multiplicityInDegree I M d =
      if Module.supportDim R M < d then 0
      else (d.factorial : ℚ) * (chiPolynomial I M).leadingCoeff := sorry

/-- When `d` is the support dimension, the unindexed algebraic multiplicity is the degree-`d`
algebraic multiplicity. -/
theorem multiplicity_eq_multiplicityInDegree_of_supportDim_eq
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (d : ℕ)
    (hd : Module.supportDim R M = d) :
    multiplicity I M = multiplicityInDegree I M d := sorry

end Local

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable [hNoetherian : IsNoetherianRing R]
include hNoetherian

/-- The multiplicity encoded by the leading coefficient of an eventual
Hilbert--Samuel `χ`-polynomial for a system of parameters is bounded by the
colength of its parameter ideal. -/
@[stacks 0BWW "Lemma 15.126.7, parameter-ideal multiplicity bound"]
theorem multiplicity_le_quotient_length_of_parameters
    {d : ℕ} (x : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x)
    (P : Polynomial ℚ) (e : ℕ)
    (hP : P.EventuallyEqNat (fun n ↦
      ((Ideal.hilbertSamuelChi (parameterIdeal x) R n).toNat : ℚ)))
    (h_lead : P.leadingCoeff = (e : ℚ) / d.factorial) :
    (e : ℕ∞) ≤ Module.length R (R ⧸ parameterIdeal x) := sorry
-- Proof strategy: compare the Hilbert--Samuel `χ`-function of the parameter
-- ideal with the standard degree-`d` binomial growth bounded by
-- `Module.length R (R ⧸ parameterIdeal x)`.  Transfer the eventual inequality
-- to the representing polynomial and compare leading coefficients; multiply
-- by `d.factorial` and transport the resulting natural-number inequality to
-- `ℕ∞`.

end Ideal.HilbertSamuel
