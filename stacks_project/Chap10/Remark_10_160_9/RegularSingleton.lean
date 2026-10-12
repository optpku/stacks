/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.Regularity.Singleton
import StacksCheckRecall

/-!
# Regular singleton sequences

@stack 032C
-/

@[expose] public section

@[stacks 032C "empty regular sequence"]
#check @RingTheory.Sequence.isRegular_nil_iff

@[stacks 032C "singleton regular sequence"]
#check @RingTheory.Sequence.isRegular_singleton_iff

@[stacks 032C "singleton in the maximal ideal"]
#check @RingTheory.Sequence.isRegular_singleton_iff_of_mem_maximalIdeal
