/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Characterization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.75.2

@stack 0658
-/

/-!
# Lemma 15.75.2: characterizing perfect derived objects

Perfectness, pseudo-coherence, finite Tor dimension, and the finite-projective model bridge are
owned at the reusable derived-category layer.
-/

/- Lemma 15.75.2 (0658): a derived module object is perfect exactly when it is pseudo-coherent
and has finite Tor dimension. -/
@[stacks 0658 "perfect iff pseudo-coherent of finite Tor dimension"]
#check @CategoryTheory.DerivedCategory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension

/- The interval-sensitive finite-projective representative supplied by the characterization. -/
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent.exists_finiteProjective_model

/- The two frequently used projections from perfectness. -/
#check @CategoryTheory.DerivedCategory.IsPerfect.isPseudoCoherent
#check @CategoryTheory.DerivedCategory.IsPerfect.hasFiniteTorDimension
