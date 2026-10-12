/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.KInjective
import StacksCheckRecall

/-!
# Lemma 15.87.11

@stack 0CQ9
-/

@[expose] public section

/-
Lemma 15.87.11 is the `AddCommGrpCat` specialization of the reusable
`DerivedLimit.Stage.TowerFunctor.essSurj_of_enoughInjectives` API.
The K-injective replacement theorem is used inside the shared specialization, not through a
chapter-local wrapper.
-/

/- Lemma 15.87.11: stagewise evaluation from the derived category of sequential inverse systems
of abelian groups to sequential towers in their derived category is essentially surjective. -/
@[stacks 0CQ9] #check
  @CategoryTheory.DerivedLimit.Stage.TowerFunctor.essSurj_of_resolution
#check @CategoryTheory.DerivedLimit.Stage.TowerFunctor.essSurj_of_enoughInjectives
