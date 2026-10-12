/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Presheaf.Subfunctor
import StacksCheckRecall.CommandCrossRef

@[expose] public section

/-!
[stacks 00V9]

Lemma 7.3.4 is the unique epi factorization through the range subpresheaf.
-/

@[stacks 00V9] #check CategoryTheory.Subfunctor.existsUnique_epiFactorization

/- Definition 7.3.5 (00VA): the image of a presheaf morphism is the canonical range subfunctor;
its inclusion and canonical factorization expose the epi factorization used in 00V9. -/
@[stacks 00VA "image subpresheaf"] #check CategoryTheory.Subfunctor.range
@[stacks 00VA "image factorization"] #check CategoryTheory.Subfunctor.toRange
@[stacks 00VA "image factorization commutes with inclusion"]
#check CategoryTheory.Subfunctor.toRange_ι
@[stacks 00VA "range of a subfunctor inclusion"] #check CategoryTheory.Subfunctor.range_ι
@[stacks 00VA "epi criterion for the range factorization"]
#check CategoryTheory.Subfunctor.epi_iff_range_eq_top
@[stacks 00VA "range factorization has maximal range"] #check CategoryTheory.Subfunctor.range_toRange
