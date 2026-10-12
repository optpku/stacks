/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.FiniteInjective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.21.7 (0H7R)

@stack 0H7R
-/

/- Lemma 15.21.7, Stacks `0H7R`: projectivity descends from a finite injective scalar extension
over a Noetherian ring. -/
@[stacks 0H7R "Lemma 15.21.7, projectivity descent along a finite injective map"]
#check @Module.Projective.of_finite_injective_baseChange
