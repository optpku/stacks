/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth.RegularSequence
import StacksCheckRecall

/-!
# Regular sequences and module depth

@stack 090R
-/

@[expose] public section

@[stacks 090R "(1)"]
#check @RingTheory.Sequence.IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one

@[stacks 090R "(2)"]
#check @RingTheory.Sequence.IsRegular.exists_append_eq_moduleDepth

@[stacks 090R "regular sequences lie in the maximal ideal"]
#check @RingTheory.Sequence.IsRegular.ofList_le_maximalIdeal
