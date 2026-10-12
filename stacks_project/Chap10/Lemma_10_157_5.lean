/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Regular
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.157.5

@stack 0567

The source statement is exactly the shared regular-to-normal theorem.
-/

@[stacks 0567]
#check @IsRegularRing.isNormalRing
