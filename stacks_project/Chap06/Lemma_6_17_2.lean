/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Sheafify
import StacksCheckRecall

@[expose] public section

/- The canonical owner is stated for every `Type`-valued presheaf and gives the isomorphism in
the reverse displayed direction. Its inverse recovers the source's identification
`ℱ.stalk x ≅ ℱ.sheafify.presheaf.stalk x`, so a local symmetric wrapper would duplicate the
canonical data without improving downstream use. -/

/- Lemma 6.17.2: sheafification preserves the stalk of a presheaf of sets at every point. -/
@[stacks 007Z "sheafification preserves stalks of set-valued presheaves"]
recall TopCat.Presheaf.sheafifyStalkIso
