/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Sheafification.MatchingFamily

/-!
# Lemma 7.10.6

Matching-family refinement is owned by the generic concrete-sheafification
API. This chapter file retains only the labeled source-facing recall.
-/

@[expose] public section

/- Lemma 7.10.6 (00W7): after pulling back a matching family, its refinement
does not depend on the selected morphism into the pullback cover. -/
@[stacks 00W7] #check @CategoryTheory.GrothendieckTopology.Meq.pullback_refine_eq

#check @CategoryTheory.GrothendieckTopology.Meq.refine_eq
