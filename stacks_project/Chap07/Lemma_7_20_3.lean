/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef

-- The reusable cocontinuous-site API is owned by this neutral ReasLib leaf.
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
import StacksCheckRecall

@[expose] public section

/- Lemma 7.20.3 (00XL): for a cocontinuous functor of sites, the sheafified pullback is left
adjoint to cocontinuous pushforward and is exact on set-valued sheaves. Both statements are
instances of the coefficient-generic ReasLib construction rather than chapter-local owners. -/
@[stacks 00XL "(1)"] #check @CategoryTheory.Functor.sheafPullbackCocontinuousAdjunction

@[stacks 00XL "(2)"] #check @CategoryTheory.Functor.sheafPullbackCocontinuous_exact

#check @CategoryTheory.Functor.sheafPullbackCocontinuous
