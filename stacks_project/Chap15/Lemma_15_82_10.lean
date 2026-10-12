/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Homology
import StacksCheckRecall

/-!
# Lemma 15.82.10

@stack 0678
-/

@[expose] public section

/-!
# Lemma 15.82.10 compatibility entry point

The derived bounded-above homology criteria for relative pseudo-coherence are
owned by `ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Homology`.
-/

/- Lemma 15.82.10 (1), tag `0678`: relative `m`-pseudo-coherence from homology. -/
@[stacks 0678 "(1), relative m-pseudo-coherence from homology"]
#check @CategoryTheory.boundedAbove_isMPseudoCoherentRelativeTo_of_homology

/- Lemma 15.82.10 (2), tag `0678`: relative pseudo-coherence from homology. -/
@[stacks 0678 "(2), relative pseudo-coherence from homology"]
#check @CategoryTheory.boundedAbove_isPseudoCoherentRelativeTo_of_homology
