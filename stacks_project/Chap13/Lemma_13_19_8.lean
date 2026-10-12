/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Bounded
import StacksCheckRecall

@[expose] public section

/- Lemma 13.19.8 is the bounded-above projective view of Mathlib's canonical
homotopy-to-derived map bijection. -/
@[stacks 064B] #check @CochainComplex.IsKProjective.Qh_map_bijective
@[stacks 064B] #check @CochainComplex.ProjectiveMinus.toDerived_map_bijective

end
