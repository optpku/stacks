module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

universe u

namespace MvPolynomial

/-- The principal quotient by a polynomial of positive total degree in two variables over a
field has Krull dimension one. -/
theorem ringKrullDim_quotient_span_singleton_eq_one
    {k : Type u} [Field k] {f : MvPolynomial (Fin 2) k} (hf : 0 < f.totalDegree) :
    ringKrullDim (MvPolynomial (Fin 2) k ⧸ Ideal.span {f}) = 1 := sorry

/-- The principal quotient by a nonzero nonunit polynomial in two variables over a field has
Krull dimension one. -/
theorem ringKrullDim_quotient_span_singleton_eq_one_of_ne_zero_not_isUnit
    {k : Type u} [Field k] {f : MvPolynomial (Fin 2) k} (h0 : f ≠ 0)
    (hu : ¬ IsUnit f) :
    ringKrullDim (MvPolynomial (Fin 2) k ⧸ Ideal.span {f}) = 1 := sorry

end MvPolynomial
