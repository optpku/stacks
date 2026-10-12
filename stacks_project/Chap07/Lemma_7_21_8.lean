/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.21.8

The source implications are the global unit and lower-shriek forms of the
fully-faithful site-functor API.
-/

@[expose] public section

/- Lemma 7.21.8 (00XU) (1): the unit of the continuous sheaf adjunction is an
isomorphism. -/
@[stacks 00XU "(1)"] #check @CategoryTheory.Functor.FullyFaithful.sheafAdjunctionContinuous_unit_isIso

/- Lemma 7.21.8 (00XU) (2): the induced lower-shriek sheaf pullback is fully
faithful. -/
@[stacks 00XU "(2)"] #check @CategoryTheory.Functor.FullyFaithful.sheafPullback_map_bijective
