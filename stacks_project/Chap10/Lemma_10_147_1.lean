module

public import ReasLib.RingTheory.Smooth.IntegralClosure
import StacksCheckRecall

@[expose] public section

/-!
# Integral representatives in polynomial quotients

@stack 03GD
-/

/- Lemma 10.147.1: for a monic polynomial f : R[X] and an R-integral element of
B[X] modulo (f), the product with the derivative of f has a representative whose coefficients
are integral over R. -/
@[stacks 03GD]
#check @Polynomial.exists_integral_coeff_representative_derivative_mul

@[stacks 03GD "source-facing coefficient representative"]
#check @exists_derivative_mul_eq_and_isIntegral_coeff
