/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.QuasiCompact
import StacksCheckRecall

@[expose] public section

/- Lemma 18.30.3 (1): sections of set-valued sheaves over a quasi-compact object of a
chosen-cover site preserve coproducts. -/
@[stacks 0935 "(1)"]
#check @CategoryTheory.Coverage.QuasiCompactObject.sheafSectionsPreservesCoproducts

/- Lemma 18.30.3 (2), owner-level refinement: module-valued evaluation preserves coproducts. -/
@[stacks 0935 "(2), module-valued"]
#check @CategoryTheory.Coverage.QuasiCompactObject.moduleEvaluationPreservesCoproducts

/- Lemma 18.30.3 (2): forgetting the scalar action recovers the stated additive-sections
functor to `AddCommGrpCat`. -/
@[stacks 0935 "(2)"]
#check @CategoryTheory.Coverage.QuasiCompactObject.moduleEvaluationForgetPreservesCoproducts

/- Sieve-saturated specializations remain available for clients starting from a Grothendieck
topology rather than a chosen coverage. -/
#check @CategoryTheory.GrothendieckTopology.QuasiCompactObject.sheafSections_preservesCoproducts
#check @SheafOfModules.evaluation_preservesCoproducts_of_quasiCompact
#check @SheafOfModules.evaluationForget_preservesCoproducts_of_quasiCompact
