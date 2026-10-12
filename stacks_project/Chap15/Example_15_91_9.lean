/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.BeauvilleLaszlo.Counterexample
import StacksCheckRecall

/-!
# Example 15.91.9: explicit completion counterexamples

The two quotient-ring presentations and their distinguished elements are concrete owners in
`ReasLib.RingTheory.AdicCompletion.BeauvilleLaszlo.Counterexample`.  This file is the source-facing
recall for the two torsion failures and their non-glueing/non-flat consequences.

@stack 0BNU
-/

-- Example 15.91.9: explicit polynomial variables and quotient presentations.
@[stacks 0BNU "counterexample variables"]
#check @BeauvilleLaszloCounterexampleVar

@[stacks 0BNU "first counterexample relation family"]
#check @firstBeauvilleLaszloCounterexampleRelation

@[stacks 0BNU "first counterexample quotient ring"]
#check @firstBeauvilleLaszloCounterexampleRing

@[stacks 0BNU "second counterexample relation family"]
#check @secondBeauvilleLaszloCounterexampleRelation

@[stacks 0BNU "second counterexample quotient ring"]
#check @secondBeauvilleLaszloCounterexampleRing

-- Example 15.91.9: the two torsion comparison failures.
@[stacks 0BNU "first torsion comparison is not injective"]
#check @firstBeauvilleLaszloCounterexample_fPowerTorsionToExtension_not_injective

@[stacks 0BNU "second torsion comparison is not surjective"]
#check @secondBeauvilleLaszloCounterexample_fPowerTorsionToExtension_not_surjective

-- Example 15.91.9: the resulting glueing and flatness failures.
@[stacks 0BNU "first counterexample is not a glueing pair"]
#check @firstBeauvilleLaszloCounterexample_not_glueing_pair

@[stacks 0BNU "second counterexample is not a glueing pair"]
#check @secondBeauvilleLaszloCounterexample_completion_not_glueing_pair

@[stacks 0BNU "first completion map is not flat"]
#check @firstBeauvilleLaszloCounterexample_completion_not_flat

@[stacks 0BNU "second completion map is not flat"]
#check @secondBeauvilleLaszloCounterexample_completion_not_flat
