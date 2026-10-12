/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Localization.Representable.BaseChange

@[expose] public section

/- Lemma 7.31.4 (04IW): for `c : U ⟶ u.obj V`, the localized slice-site
inverse image agrees with pullback along the canonical representable
base-change map. This is exactly the reusable functor-level comparison owned
by ReasLib. -/
@[stacks 04IW] #check @CategoryTheory.GrothendieckTopology.RepresentableLocalization.sheafPullbackOverPullback
