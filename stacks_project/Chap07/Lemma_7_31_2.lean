/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Localization.Representable.BaseChange

@[expose] public section

/- Lemma 7.31.2 (04IU): for a continuous functor of sites `u : D ⥤ C`,
representable localization at `V` and at `u.obj V` identifies the slice-site
inverse image with the inverse image of the localized morphism of topoi. This
is exactly the reusable base-change comparison owned by ReasLib. -/
@[stacks 04IU] #check @CategoryTheory.GrothendieckTopology.RepresentableLocalization.sheafPullbackAtImage
