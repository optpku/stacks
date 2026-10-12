/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Frobenius.SeparableRoots
import StacksCheckRecall

@[expose] public section

/- Lemma 9.28.2 (Tag 031V): a root of a separable polynomial over a characteristic-`p` field
whose coefficients are `p`th powers is itself a `p`th power. The general Frobenius-image and
minimal-polynomial forms are owned by `FieldExtension`. -/
#check Polynomial.Frobenius.range
#check Polynomial.Frobenius.mem_range_iff_coeff_eq_pow
#check FieldExtension.Frobenius.memPowRangeOfIsRoot
#check FieldExtension.Frobenius.existsPthRootOfIsRoot
@[stacks 031V]
#check FieldExtension.SeparableRoot.existsPthRootOfCoefficientsArePthPowers
#check FieldExtension.SeparableRoot.existsPthRootOfMinpolyCoefficientsArePthPowers
