/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Over.Pushforward

/-!
# Legacy compatibility module for Lemma 7.28.1

Slice-site pushforward comparisons are owned by ReasLib.
-/

@[expose] public section

#check @CategoryTheory.Functor.sheafPushforwardOverPost
#check @CategoryTheory.Functor.sheafPushforwardOverPostComp
