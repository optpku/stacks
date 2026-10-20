module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Finite.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

universe u

noncomputable section

namespace MvPolynomial

/-- The `k`-algebra map `Polynomial k →ₐ[k] MvPolynomial (Fin 2) k ⧸ Ideal.span {f}`
sending `Polynomial.X` to the class of `C α * X 0 + C β * X 1`. -/
def linearFormAeval {k : Type u} [CommRing k] (f : MvPolynomial (Fin 2) k) (α β : k) :
    Polynomial k →ₐ[k] MvPolynomial (Fin 2) k ⧸ Ideal.span {f} :=
  Polynomial.aeval (Ideal.Quotient.mk (Ideal.span {f}) (C α * X 0 + C β * X 1))

/-- `linearFormAeval f α β` sends `Polynomial.X` to the class of `C α * X 0 + C β * X 1`. -/
theorem linearFormAeval_X {k : Type u} [CommRing k] (f : MvPolynomial (Fin 2) k) (α β : k) :
    linearFormAeval f α β Polynomial.X =
      Ideal.Quotient.mk (Ideal.span {f}) (C α * X 0 + C β * X 1) := by
  unfold linearFormAeval
  exact Polynomial.aeval_X _

/-- A nonconstant polynomial in two variables over an infinite field admits a linear form
whose evaluation map to the quotient by that polynomial is finite. -/
theorem exists_linearFormAeval_finite {k : Type u} [Field k] [Infinite k]
    (f : MvPolynomial (Fin 2) k) (hf : 0 < f.totalDegree) :
    ∃ α β : k, (linearFormAeval f α β).Finite := sorry

end MvPolynomial
