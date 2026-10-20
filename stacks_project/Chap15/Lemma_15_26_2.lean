module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.StrictTransform.Valuation
import StacksCheckRecall

/-!
# Lemma 15.26.2

@stack 053I

The valuation-theoretic flattening statement and the required source-chart actions are owned by
the reusable strict-transform API.
-/

@[expose] public section

#check @AffineBlowupChart.BaseChange.instAlgebraSourceChartTarget
#check @AffineBlowupChart.BaseChange.instModuleSourceChartStrictTransform

/- Lemma 15.26.2: a valuation-dominated local domain admits an affine blowup chart on which the
strict-transform algebra and module are flat and finitely presented in the stated senses. -/
@[stacks 053I "Lemma 15.26.2"]
#check @AffineBlowupChart.Valuation.existsFlatFinitelyPresentedStrictTransforms
