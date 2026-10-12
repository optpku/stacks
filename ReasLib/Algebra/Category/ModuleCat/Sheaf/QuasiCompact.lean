/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import ReasLib.CategoryTheory.Sites.QuasiCompact.Coproducts
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sections of module sheaves over quasi-compact site objects

This file lifts the coproduct-preservation theorem for set-valued sheaf sections to module-valued
sections.  The module-valued functor is the reusable owner; forgetting scalars recovers the
abelian-group-valued formulation used in the Stacks Project.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe r w v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Module-valued refinement of Lemma 18.30.3 (2): evaluation of module sheaves at a quasi-compact
site object preserves arbitrary coproducts. -/
@[stacks 0935 "(2), sieve-saturated module-valued specialization"]
theorem evaluation_preservesCoproducts_of_quasiCompact
    (R : Sheaf J RingCat.{r}) {W : C} (hW : J.QuasiCompactObject W) (I : Type w) :
    PreservesColimitsOfShape (Discrete I)
      (evaluation.{r} R (op W)) := sorry

/-- Lemma 18.30.3 (2): after forgetting scalars, sections of module sheaves over a quasi-compact
site object preserve arbitrary direct sums. -/
@[stacks 0935 "(2), sieve-saturated specialization"]
theorem evaluationForget_preservesCoproducts_of_quasiCompact
    (R : Sheaf J RingCat.{r}) {W : C} (hW : J.QuasiCompactObject W) (I : Type w) :
    PreservesColimitsOfShape (Discrete I)
      (evaluation.{r} R (op W) ⋙
        forget₂ (ModuleCat.{r} (R.1.obj (op W))) AddCommGrpCat.{r}) :=
  sorry

namespace Evaluation

/-- Lemma 17.3.5 at the site level: over a quasi-compact object, the canonical map from the
coproduct of module sections to the sections of the coproduct is an isomorphism. -/
@[stacks 01AI "site-theoretic form"]
theorem sigmaComparison_isIso_of_quasiCompact
    (R : Sheaf J RingCat.{r}) {W : C} (hW : J.QuasiCompactObject W)
    {I : Type w} (F : I → SheafOfModules.{r} R) [HasCoproduct F]
    [HasCoproduct (fun i ↦ (evaluation.{r} R (op W)).obj (F i))] :
    IsIso (sigmaComparison (evaluation.{r} R (op W)) F) := sorry

end Evaluation

end SheafOfModules

namespace CategoryTheory.Coverage.QuasiCompactObject

variable {C : Type u} [Category.{v} C] {K : Coverage C} {W : C}

/-- Lemma 18.30.3 (0935) (2), module-valued form: evaluation over a quasi-compact object of a
chosen-cover site preserves arbitrary coproducts of module sheaves. -/
@[stacks 0935 "(2), module-valued"]
theorem moduleEvaluationPreservesCoproducts
    (hW : K.QuasiCompactObject W)
    (R : Sheaf K.toGrothendieck RingCat.{r}) (I : Type w) :
    PreservesColimitsOfShape (Discrete I)
      (SheafOfModules.evaluation.{r} R (op W)) := sorry

/-- Lemma 18.30.3 (0935) (2): after forgetting scalars, evaluation over a quasi-compact object
of a chosen-cover site preserves arbitrary direct sums. -/
@[stacks 0935 "(2)"]
theorem moduleEvaluationForgetPreservesCoproducts
    (hW : K.QuasiCompactObject W)
    (R : Sheaf K.toGrothendieck RingCat.{r}) (I : Type w) :
    PreservesColimitsOfShape (Discrete I)
      (SheafOfModules.evaluation.{r} R (op W) ⋙
        forget₂ (ModuleCat.{r} (R.1.obj (op W))) AddCommGrpCat.{r}) := sorry

end CategoryTheory.Coverage.QuasiCompactObject
