module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.Regularity.ClosedFiber

@[expose] public section

/-!
# Lemma 10.99.3

For a flat local map with Noetherian target, regularity of a finite sequence on the quotient
closed fiber lifts to regularity in the target and flatness of every nonempty prefix quotient.
The list-level theorem is owned by `RingTheory.Sequence.ClosedFiber`.

@stack 00MG
-/

@[stacks 00MG "regular sequences lift from a Noetherian closed fiber"]
#check @RingTheory.Sequence.ClosedFiber.isRegular_flat_prefixes
