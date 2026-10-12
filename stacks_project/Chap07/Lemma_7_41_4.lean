/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Precoverage.Reflection

@[expose] public section

/-!
# Lemma 7.41.4

The selected-cover presentation bridge is owned by the reusable precoverage
reflection API.
-/

/- Lemma 7.41.4 (1) (04D9): cover-dense continuous direct image for
precoverage-presented sites reflects monomorphisms. -/
@[stacks 04D9 "(1)"] #check @CategoryTheory.Functor.Precoverage.IsContinuous.reflectsMonomorphisms

/- Lemma 7.41.4 (2) (04D9): under sheafification, the same direct image
reflects epimorphisms. -/
@[stacks 04D9 "(2)"] #check @CategoryTheory.Functor.Precoverage.IsContinuous.reflectsEpimorphisms
