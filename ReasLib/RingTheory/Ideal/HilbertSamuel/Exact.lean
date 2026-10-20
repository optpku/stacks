/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Degree
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Multiplicity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hilbert--Samuel Functions in Short Exact Sequences

@stack 00K6
@stack 00KC

The Artin--Rees decomposition and its polynomial-degree consequences are
packaged here independently of any chapter-local proof staging.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace Ideal.HilbertSamuel

namespace ShortExact

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

section MiddleFinite

variable [Module.Finite R S.X₂]

/-- A short exact sequence admits a finite-colength submodule and a shift that
simultaneously give eventual `χ`- and `φ`-decompositions. -/
@[stacks 00K6]
theorem exists_decomposition (I : Ideal R) (hI : I.IsIdealOfDefinition)
    (hS : S.ShortExact) :
    ∃ (N : Submodule R S.X₁) (c : ℕ),
      IsFiniteLength R (S.X₁ ⧸ N) ∧
        (∀ n ≥ c,
          I.hilbertSamuelChi S.X₂ n =
            I.hilbertSamuelChi S.X₃ n + I.hilbertSamuelChi N (n - c) +
              Module.length R (S.X₁ ⧸ N)) ∧
        (∀ n ≥ c,
          I.hilbertSamuelPhi S.X₂ n =
            I.hilbertSamuelPhi S.X₃ n + I.hilbertSamuelPhi N (n - c)) := sorry

/-- The `χ`-projection of the simultaneous short-exact Hilbert--Samuel
decomposition. -/
@[stacks 00K6 "short-exact chi decomposition"]
theorem exists_chi_decomposition (I : Ideal R)
    (hI : I.IsIdealOfDefinition) (hS : S.ShortExact) :
    ∃ (N : Submodule R S.X₁) (c : ℕ),
      IsFiniteLength R (S.X₁ ⧸ N) ∧
        ∀ n ≥ c,
          I.hilbertSamuelChi S.X₂ n =
            I.hilbertSamuelChi S.X₃ n + I.hilbertSamuelChi N (n - c) +
              Module.length R (S.X₁ ⧸ N) := sorry

/-- The `φ`-projection of the simultaneous short-exact Hilbert--Samuel
decomposition. -/
@[stacks 00K6 "short-exact phi decomposition"]
theorem exists_phi_decomposition (I : Ideal R)
    (hI : I.IsIdealOfDefinition) (hS : S.ShortExact) :
    ∃ (N : Submodule R S.X₁) (c : ℕ),
      IsFiniteLength R (S.X₁ ⧸ N) ∧
        ∀ n ≥ c,
          I.hilbertSamuelPhi S.X₂ n =
              I.hilbertSamuelPhi S.X₃ n + I.hilbertSamuelPhi N (n - c) := sorry

end MiddleFinite

section Degree

variable [Module.Finite R S.X₂]

/-- In a short exact sequence, the Hilbert--Samuel `χ`-polynomial error has
degree below the polynomial of the first term when that term has infinite length. -/
@[stacks 00KC "(1)"]
theorem chi_error_degree_lt
    {P₁ P₂ P₃ : Polynomial ℚ} (I : Ideal R)
    (hI : I.IsIdealOfDefinition) (hS : S.ShortExact)
    (hP₁ : P₁.EventuallyEqNat
      (fun n ↦ ((I.hilbertSamuelChi S.X₁ n).toNat : ℚ)))
    (hP₂ : P₂.EventuallyEqNat
      (fun n ↦ ((I.hilbertSamuelChi S.X₂ n).toNat : ℚ)))
    (hP₃ : P₃.EventuallyEqNat
      (fun n ↦ ((I.hilbertSamuelChi S.X₃ n).toNat : ℚ)))
    (hX₁ : ¬ IsFiniteLength R S.X₁) :
    (P₂ - P₃ - P₁).degree < P₁.degree := sorry

/-- In a short exact sequence, the middle Hilbert--Samuel `χ`-polynomial has
degree equal to the maximum of the endpoint degrees. -/
@[stacks 00KC "(2)"]
theorem chi_degree_eq_max
    {P₁ P₂ P₃ : Polynomial ℚ} (I : Ideal R)
    (hI : I.IsIdealOfDefinition) (hS : S.ShortExact)
    (hP₁ : P₁.EventuallyEqNat
      (fun n ↦ ((I.hilbertSamuelChi S.X₁ n).toNat : ℚ)))
    (hP₂ : P₂.EventuallyEqNat
      (fun n ↦ ((I.hilbertSamuelChi S.X₂ n).toNat : ℚ)))
    (hP₃ : P₃.EventuallyEqNat
      (fun n ↦ ((I.hilbertSamuelChi S.X₃ n).toNat : ℚ))) :
    P₂.degree = max P₁.degree P₃.degree := sorry

end Degree

/-! ### Canonical polynomial and degree consequences -/

section Canonical

variable [Module.Finite R S.X₂]

/-- The error formed from canonical Hilbert--Samuel `χ`-polynomials has lower
degree whenever the left term has infinite length. -/
@[stacks 00KC "canonical companion to (1)"]
theorem chiPolynomial_error_degree_lt
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (hS : S.ShortExact)
    (hX₁ : ¬ IsFiniteLength R S.X₁) :
    (chiPolynomial I S.X₂ - chiPolynomial I S.X₃ - chiPolynomial I S.X₁).degree <
      (chiPolynomial I S.X₁).degree := sorry

/-- The Hilbert--Samuel degree of the middle term of a short exact sequence of
finite modules is the maximum of the endpoint degrees. -/
@[stacks 00KC "(3)"]
theorem degree_eq_max (hS : S.ShortExact) :
    degree R S.X₂ = max (degree R S.X₁) (degree R S.X₃) := sorry

end Canonical

section Additivity

/-- For an ideal of definition, degree-`d` Hilbert--Samuel multiplicity is additive
along a short exact sequence of finite modules whenever `d` is at least the support
dimension of the middle module. -/
@[stacks 0AZW]
theorem multiplicity_eq_add [Module.Finite R S.X₁] [Module.Finite R S.X₂]
    [Module.Finite R S.X₃] (I : Ideal R) (hI : I.IsIdealOfDefinition)
    (hS : S.ShortExact) (d : ℕ) (hd : Module.supportDim R S.X₂ ≤ d) :
    multiplicityInDegree I S.X₂ d =
      multiplicityInDegree I S.X₁ d + multiplicityInDegree I S.X₃ d := sorry

end Additivity

end ShortExact

end Ideal.HilbertSamuel
