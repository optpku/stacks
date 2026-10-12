/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.PseudoCoherent
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.76.4: pseudo-coherence across a nilpotent thickening

@stack 0H76

The explicit-ring-homomorphism theorem is owned by
`CategoryTheory.DerivedCategory.IsPseudoCoherent.extension_iff`.
-/

open CategoryTheory

/- Lemma 15.76.4 (0H76): derived extension along a surjection with nilpotent kernel reflects and
preserves pseudo-coherence. -/
@[stacks 0H76 "Lemma 15.76.4"]
#check @DerivedCategory.IsPseudoCoherent.extension_iff

#check @DerivedCategory.IsPseudoCoherent.extension
