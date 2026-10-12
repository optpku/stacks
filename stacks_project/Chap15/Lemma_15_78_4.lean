/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ProjectiveAmplitude.Recognition
import StacksCheckRecall

/-!
# Lemma 15.78.4 (0G9A)

@stack 0G9A

The projective-amplitude criterion is owned by the derived-category recognition leaf. This
Chapter file is its direct official-label recall.
-/

@[expose] public section

/- Lemma 15.78.4 (0G9A): projective amplitude, perfect Tor-amplitude, and finite-presentation
derived-Ext vanishing are equivalent for pseudo-coherent objects. -/
@[stacks 0G9A "Lemma 15.78.4"]
#check @CategoryTheory.projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent

#check @CategoryTheory.projectiveAmplitudeIn_ext_vanishing_tfae

#print axioms CategoryTheory.projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent
