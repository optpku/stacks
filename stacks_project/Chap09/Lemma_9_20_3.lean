module

public import ReasLib.FieldTheory.Minpoly.Norm
public import Mathlib.RingTheory.Trace.Basic
import StacksCheckRecall

@[expose] public section

/- Lemma 9.20.3 (Tag 0BIH): in a finite field extension, the norm is the signed constant
coefficient of the minimal polynomial raised to the degree over the simple subextension, and the
trace is minus the corresponding multiple of the next coefficient. -/
@[stacks 0BIH]
#check Algebra.norm_eq_sign_mul_minpoly_coeff_zero_pow_finrank_adjoin
#check trace_eq_finrank_mul_minpoly_nextCoeff
