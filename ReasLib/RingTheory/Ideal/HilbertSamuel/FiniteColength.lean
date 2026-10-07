module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Degree
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Finiteness
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hilbert--Samuel Polynomials and Finite-Colength Submodules

@stack 00KB

This file contains the reusable polynomial-growth consequences of replacing a
finite module by a finite-colength submodule.
-/

@[expose] public section

open Filter

universe u v

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- An eventual Hilbert--Samuel `χ`-polynomial of a module of infinite length
has positive degree. -/
theorem chiPolynomial_degree_pos (I : Ideal R) (hI : I.IsIdealOfDefinition)
    {P : Polynomial ℚ} (hM : ¬ IsFiniteLength R M)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((I.hilbertSamuelChi M n).toNat : ℚ)) :
    0 < P.degree := sorry

/-- For an infinite-length finite module and a finite-colength submodule, the
difference of their eventual `χ`-polynomials has degree below either one. -/
@[stacks 00KB]
theorem chiPolynomial_sub_degree_lt (I : Ideal R)
    (hI : I.IsIdealOfDefinition) (N : Submodule R M)
    (hM : ¬ IsFiniteLength R M) (hquot : IsFiniteLength R (M ⧸ N))
    {P P' : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((I.hilbertSamuelChi M n).toNat : ℚ))
    (hP' : ∀ᶠ n : ℕ in atTop,
      P'.eval (n : ℚ) = ((I.hilbertSamuelChi N n).toNat : ℚ)) :
    (P - P').degree < P.degree ∧ (P - P').degree < P'.degree := sorry

/-- A finite module and an infinite-length finite-colength submodule have
eventual Hilbert--Samuel `χ`-polynomials of the same degree. -/
theorem chiPolynomial_degree_eq_of_finiteColength
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (N : Submodule R M)
    (hM : ¬ IsFiniteLength R M) (hquot : IsFiniteLength R (M ⧸ N))
    {P P' : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((I.hilbertSamuelChi M n).toNat : ℚ))
    (hP' : ∀ᶠ n : ℕ in atTop,
      P'.eval (n : ℚ) = ((I.hilbertSamuelChi N n).toNat : ℚ)) :
    P.degree = P'.degree := sorry

end Ideal.HilbertSamuel
