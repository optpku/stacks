/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.StrictTransform
import StacksCheckRecall

/-!
# Lemma 15.26.3

@stack 0CZM

The Fitting-ideal calculation for strict transforms is owned by the reusable affine
blowup-chart API.
-/

@[expose] public section

/- Lemma 15.26.3: on a chart indexed by the `k`th Fitting ideal, the `k`th Fitting ideal of the
strict transform is the unit ideal. -/
@[stacks 0CZM "Lemma 15.26.3"]
#check @AffineBlowupChart.StrictTransform.fittingIdeal_eq_top
