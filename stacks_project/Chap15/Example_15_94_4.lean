/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.AdicCompletion.PolynomialCounterexample
import StacksCheckRecall

/-!
# Example 15.94.4 (0G3F)

The completed substitution, its cokernel, and the explicit geometric-series class are owned by
`ReasLib.Algebra.Homology.DerivedCategory.Completeness.AdicCompletion.PolynomialCounterexample`.

@stack 0G3F
-/

@[expose] public section

/- Example 15.94.4 (1): the module is the cokernel of completed substitution by `X ↦ p * X`. -/
@[stacks 0G3F "(1), completed-substitution cokernel"]
#check @PadicPolynomialCompletion.substitutionCokernel

/- Example 15.94.4 (2): this cokernel is derived complete. -/
@[stacks 0G3F "(2), derived completeness"]
#check @PadicPolynomialCompletion.substitutionCokernel_isDerivedComplete

/- Example 15.94.4 (3): the compatible truncations define the concrete geometric series. -/
@[stacks 0G3F "(3), geometric-series completion element"]
#check @PadicPolynomialCompletion.geometricSeries

/- Example 15.94.4 (4): the geometric-series class in the cokernel is nonzero. -/
@[stacks 0G3F "(4), nonzero geometric-series class"]
#check @PadicPolynomialCompletion.geometricClass_ne_zero

/- Example 15.94.4 (5): that class lies in every principal-power multiple. -/
@[stacks 0G3F "(5), geometric-series class in every power"]
#check @PadicPolynomialCompletion.geometricClass_mem_pow

/- Example 15.94.4 (6): the cokernel is not ordinarily adically complete. -/
@[stacks 0G3F "(6), failure of ordinary adic completeness"]
#check @PadicPolynomialCompletion.substitutionCokernel_not_isAdicComplete

#check @PadicPolynomialCompletion.substitution
#check @PadicPolynomialCompletion.geometricTruncation
#check @PadicPolynomialCompletion.geometricToQuotient
#check @PadicPolynomialCompletion.geometricToQuotient_compatible
#check @PadicPolynomialCompletion.geometricSeries_eval
#check @PadicPolynomialCompletion.geometricClass
