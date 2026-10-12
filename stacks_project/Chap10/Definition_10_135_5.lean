/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CompleteIntersection.Basic
import StacksCheckRecall

/-!
# Definition 10.135.5

@stack 00SD
-/

@[expose] public section

/- Definition 10.135.5 is owned by `ReasLib.RingTheory.CompleteIntersection.Basic`. -/
@[stacks 00SD "ring-hom regular-sequence kernel"]
#check @RingHom.KernelIsGeneratedByRegularSequence
@[stacks 00SD "ideal regular-sequence kernel"]
#check @Ideal.IsGeneratedByRegularSequence
@[stacks 00SD]
#check @Algebra.IsCompleteIntersectionOver
