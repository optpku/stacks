/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselization
import StacksCheckRecall

@[expose] public section

/-!
# Strict Henselization Owner Recall

The reusable strict-henselization owner is defined in ReasLib so that downstream chapters do not
depend on the Chapter 10 construction file.

@stack 04GP
-/

/- Canonical recall of the shared strict-henselization owner. -/
@[stacks 04GP "strict henselization owner"]
#check @IsStrictHenselizationOf
