/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.BoundedAbove
import StacksCheckRecall

/-!
# Lemma 15.82.9

@stack 0677
-/

@[expose] public section

/-!
# Lemma 15.82.9 compatibility entry point

The absolute and presentationwise bounded-above pseudo-coherence criteria are
owned by the `PseudoCoherent.BoundedAbove` and
`PseudoCoherent.Relative.BoundedAbove` leaves.
-/

/- Lemma 15.82.9 (1), tag `0677`: relative `m`-pseudo-coherence for bounded-above complexes. -/
@[stacks 0677 "(1), bounded-above relative m-pseudo-coherence"]
#check @CategoryTheory.cochainComplex_isMPseudoCoherentRelativeTo_of_boundedAbove_of_termwise

/- Lemma 15.82.9 (2), tag `0677`: relative pseudo-coherence for bounded-above complexes. -/
@[stacks 0677 "(2), bounded-above relative pseudo-coherence"]
#check @CategoryTheory.cochainComplex_isPseudoCoherentRelativeTo_of_boundedAbove_of_termwise
