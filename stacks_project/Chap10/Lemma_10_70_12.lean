/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Valuation
import StacksCheckRecall

/-! @stack 052M -/

/-!
# Lemma 10.70.12 recall

Valuation approximations by affine blowup charts are owned by
`AffineBlowupChart.Valuation`.  The source's directed-family and union claims
are exposed there as separate reusable statements.
-/

@[expose] public section

/- Lemma 10.70.12 (052M): a dominating valuation subring is the directed
union of its finite affine blowup approximations with nontrivial closed fiber. -/
@[stacks 052M "valuation approximation data"]
#check @AffineBlowupChart.Valuation.IsApproximation

@[stacks 052M "nontrivial approximation fiber"]
#check @AffineBlowupChart.Valuation.fiber_nontrivial_of_fractionSubring_le

@[stacks 052M "directed valuation approximations"]
#check @AffineBlowupChart.Valuation.directed

@[stacks 052M "valuation approximation supremum"]
#check @AffineBlowupChart.Valuation.iSup_eq
