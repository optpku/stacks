/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Over.Pushforward
public import ReasLib.CategoryTheory.Sites.Over.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Topos.Localized.BaseChange
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.28.1

The slice-site and localized-topos infrastructure used by this lemma is owned
by `ReasLib`; this Chapter 7 entry is a source-facing recall block.
-/

@[expose] public section

namespace CategoryTheory

/- Lemma 7.28.1 (03CF): for a morphism of sites represented by a continuous
functor `u : D ⥤ C` and `V : D`, the induced functor `Over.post u` defines the
morphism between the slice sites.  Its direct and inverse images commute with
the localization functors. -/
@[stacks 03CF] #check @IsMorphismOfSites.overPost

@[stacks 03CF] #check @Functor.sheafPushforwardOverPost

@[stacks 03CF] #check @Functor.sheafPushforwardOverPostComp

@[stacks 03CF] #check @Functor.Localized.inverseImageOverPullback

end CategoryTheory
