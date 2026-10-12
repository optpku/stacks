/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart
import StacksCheckRecall

@[expose] public section

/-!
## Definition 10.70.1 (052Q)

@stack 052Q

The blowup algebra is the canonical mathlib Rees algebra `reesAlgebra I`.
Its explicit grading by the powers `I ^ n` and the affine chart `R[I / a]`
are owned by `ReasLib.RingTheory.ReesAlgebra`; this chapter entry is a
source-facing recall facade.
-/

/- Definition 10.70.1 (1): the Rees algebra of `I` is graded by the powers
`I ^ n`. -/
@[stacks 052Q "(1), Rees algebra"]
#check @reesAlgebra
@[stacks 052Q "(1), Rees grading"]
#check @ReesAlgebra.Grading.grade
@[stacks 052Q "(1), degree-one piece"]
#check @ReesAlgebra.Grading.degreeOne

/- Definition 10.70.1 (2): `R[I / a]` is the degree-zero homogeneous
localization of the Rees algebra at the degree-one element determined by `a`. -/
@[stacks 052Q "(2), affine blowup algebra"]
#check @affineBlowupChart
