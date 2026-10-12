/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.Regularity.ClosedFiber

@[expose] public section

/-!
# Lemma 10.128.6

For a flat essentially finitely presented local map, regularity of a finite sequence on the
canonical closed fiber lifts to regularity in the target and flatness of every nonempty prefix
quotient.  The reusable owner is
`RingTheory.Sequence.ClosedFiber.isRegular_flat_prefixes_of_essFinitePresentation`.

@stack 0470
-/

@[stacks 0470 "regular sequences lift from an essentially finitely presented closed fiber"]
#check @RingTheory.Sequence.ClosedFiber.isRegular_flat_prefixes_of_essFinitePresentation
