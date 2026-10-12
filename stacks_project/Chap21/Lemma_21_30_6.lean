/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Equalizer
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.30.6

The equalizer-descent statement is owned by the reusable topology-comparison cohomology leaf.
It uses `Sheaf.cohomologyOverObject` and the raised cohomology presheaf, so the object and morphism
universes of the site need not coincide. This chapter file only recalls the source-facing API.
-/

open CategoryTheory
open CategoryTheory.GrothendieckTopology.TopologyComparison
open scoped CategoryTheory.GrothendieckTopology

/- Lemma 21.30.6 (0EZD): an equalizer class in
`H'_{τ'}(X, ℱ')` for a singleton `τ`-cover becomes zero after a `τ'`-cover of `Y`. -/
@[stacks 0EZD]
#check @Cohomology.equalizerVanishes

@[stacks 0EZD]
#check @Situation.BaseChange.canonical

end
