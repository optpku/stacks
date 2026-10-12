/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Reflexive
import StacksCheckRecall

/-!
# Lemma 15.23.14

@stack 0AV9

The local-depth criterion is owned by the reusable linear-map API.  This file records the
textbook entry without rebuilding its associated-prime proof.
-/

@[expose] public section

/- Lemma 15.23.14: a map from a finite module to a torsion-free module over a Noetherian domain
is an isomorphism when, at each prime, it is locally an isomorphism or the source has depth at
least two. -/
@[stacks 0AV9 "Lemma 15.23.14"]
#check @LinearMap.bijective_of_localized_bijective_or_depth_ge_two
