/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Stalks
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- The canonical owner works for presheaves valued in any category with the required filtered
colimits. Taking the coefficient category to be `Type u` recovers the source's presheaves of sets,
so a local specialization would duplicate data and obscure the reusable stalk-pullback isomorphism. -/

/- Lemma 6.21.4: for a continuous map `f : X ⟶ Y`, a presheaf of sets `𝒢` on `Y`, and a point
`x : X`, there is a canonical bijection between `𝒢.stalk (f x)` and the stalk at `x` of the
pullback presheaf. -/
@[stacks 008G "stalks of inverse-image presheaves"]
recall TopCat.Presheaf.stalkPullbackIso
