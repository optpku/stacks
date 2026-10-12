/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import StacksCheckRecall.CommandCrossRef

@[expose] public section

/-
Lemma 7.28.7 (0FN2) (1): a strictly commutative square of continuous site functors induces the
canonical comparison between the two composites of sheaf pushforwards.
-/
@[stacks 0FN2 "(1)"] #check @CategoryTheory.Functor.ContinuousSquare.pushforwardIso

/-
Lemma 7.28.7 (0FN2) (2): under the factorwise left-Kan-extension hypotheses, the preceding
comparison has the canonical mate between the composites of sheaf pullbacks.
-/
@[stacks 0FN2 "(2)"] #check @CategoryTheory.Functor.ContinuousSquare.pullbackIso
