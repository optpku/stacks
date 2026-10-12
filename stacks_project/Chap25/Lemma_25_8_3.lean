/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Properties
import StacksCheckRecall

/-!
# Covering degrees and face maps

These pointwise consequences are owned by the shared hypercovering property API.
-/

open CategoryTheory

/- Lemma 25.8.3 (0DEQ) (1): every degree family of a hypercovering covers its target. -/
@[stacks 0DEQ "every hypercovering degree is covering"]
#check @Hypercovering.family_isCovering

/- Lemma 25.8.3 (0DEQ) (2): every face map of a hypercovering is covering. -/
@[stacks 0DEQ "hypercovering face maps are covering"]
#check @Hypercovering.faceMap_isCovering
