/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Action.SheafEquivalence

/-!
# Canonical recall for Proposition 7.9.1

The equivalence between `G`-sets and sheaves on their jointly-surjective site belongs to ReasLib,
where its left-regular-sections quasi-inverse and comparison API can be imported independently of
this chapter.
-/

@[expose] public section

open CategoryTheory

/- Proposition 7.9.1 (00W0): for a group `G`, the Yoneda functor from `G`-sets to sheaves for
the jointly-surjective topology is an equivalence. -/
@[stacks 00W0] #check @CategoryTheory.Action.SheafEquivalence.yonedaIsEquivalence
