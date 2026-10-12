/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import ReasLib.RingTheory.Ideal.OfList
public import ReasLib.RingTheory.Sequence.Regularity.Ideal
import StacksCheckRecall

@[expose] public section

/-!
Definition 10.68.1 (Tag 00LF): a regular sequence in an ideal is recalled
through the canonical `RingTheory.Sequence.IsRegular` predicate together with
the reusable `Ideal.ofList_le_iff` and
`RingTheory.Sequence.isRegular_in_ideal_iff` bridges.

@stack 00LF
-/
@[stacks 00LF "regular sequences"]
#check @RingTheory.Sequence.IsRegular
@[stacks 00LF "list-generated ideal"]
#check @Ideal.ofList_le_iff
@[stacks 00LF "regular sequence in an ideal"]
#check @RingTheory.Sequence.isRegular_in_ideal_iff
