/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.Regularity.Exact
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.68.8

@stack 0F1T

The short-exact-sequence extension theorem is recalled directly from its ReasLib owner.
-/

@[stacks 0F1T "regular sequences are stable under extensions"]
#check @CategoryTheory.ShortComplex.ShortExact.isRegular_X₂

#check @RingTheory.Sequence.IsRegular
