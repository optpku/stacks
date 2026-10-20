module

public import ReasLib.RingTheory.KrullDimension.Polynomial.PrincipalQuotient
public import Mathlib.Data.Complex.Basic
import StacksCheckRecall

@[expose] public section

/- Exercise 111.17.2: the quotient of ℂ[x, y] by a nonconstant polynomial has
Krull dimension one. -/
@[stacks 076I] #check (MvPolynomial.ringKrullDim_quotient_span_singleton_eq_one :
  ∀ {f : MvPolynomial (Fin 2) ℂ}, 0 < f.totalDegree →
    ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ Ideal.span {f}) = 1)
