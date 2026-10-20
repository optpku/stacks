/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Laurent polynomials modulo polynomials

The additive quotient by the polynomial submodule records the negative powers of a Laurent
polynomial.
-/

@[expose] public section

open scoped LaurentPolynomial

noncomputable section

universe u

namespace LaurentPolynomial

variable (R : Type u) [CommRing R]

/-- The submodule of Laurent polynomials that come from ordinary polynomials. -/
abbrev polynomialRange : Submodule R (LaurentPolynomial R) :=
  LinearMap.range (Polynomial.toLaurentAlg : Polynomial R →ₐ[R] LaurentPolynomial R).toLinearMap

/-- The additive quotient of Laurent polynomials by the polynomial submodule. -/
abbrev quotientByPolynomials : Type u :=
  LaurentPolynomial R ⧸ polynomialRange R

/-- The class of a Laurent polynomial modulo the polynomial submodule. -/
def quotientByPolynomialsMk (f : LaurentPolynomial R) : quotientByPolynomials R :=
  Submodule.Quotient.mk f

/-- An ordinary polynomial represents zero in the quotient by polynomials. -/
theorem quotientByPolynomialsMk_toLaurent (p : Polynomial R) :
    quotientByPolynomialsMk R (Polynomial.toLaurent p) = 0 := by
  change (Submodule.Quotient.mk (Polynomial.toLaurent p) : quotientByPolynomials R) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change (Polynomial.toLaurentAlg p) ∈ _
  exact LinearMap.mem_range_self _ p

/-- The classes of the negative Laurent powers, indexed by positive integers. -/
def negativePowerClass : {n : ℕ // 0 < n} → quotientByPolynomials R :=
  fun n ↦ quotientByPolynomialsMk R (LaurentPolynomial.T (-(n : ℤ)))

/-- Evaluation of a negative-power class. -/
theorem negativePowerClass_apply (n : {n : ℕ // 0 < n}) :
    negativePowerClass R n = quotientByPolynomialsMk R (LaurentPolynomial.T (-(n : ℤ))) := rfl

/-- The negative-power classes are linearly independent in the quotient. -/
theorem negativePowerClass_linearIndependent :
    LinearIndependent R (negativePowerClass R) := by
  sorry

/-- The negative-power classes span the quotient by polynomials. -/
theorem negativePowerClass_span :
    Submodule.span R (Set.range (negativePowerClass R)) = ⊤ := by
  sorry

/-- Finite linear combinations of the negative-power classes give a bijection with the
quotient by polynomials. -/
theorem negativePowerClass_bijective :
    Function.Bijective (Finsupp.linearCombination R (negativePowerClass R)) := by
  sorry

end LaurentPolynomial

end
