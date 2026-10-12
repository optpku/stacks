/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Degree.Units

@[expose] public section

universe u

open scoped LaurentPolynomial Polynomial

namespace LaurentPolynomial

/-- Every algebra homomorphism from a Laurent polynomial ring over a field to a polynomial ring
sends the Laurent generator `T 1` to a constant polynomial. -/
theorem map_T_eq_C {k : Type u} [Field k] (φ : k[T;T⁻¹] →ₐ[k] k[X]) :
    ∃ c : k, φ (T 1) = Polynomial.C c := sorry

end LaurentPolynomial
