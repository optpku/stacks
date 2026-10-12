/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Evaluation
import StacksCheckRecall

/-!
# Lemma 15.55.7: injectivity of character evaluation

@stack 01DB

Injectivity depends only on the underlying additive group.  The arbitrary-ring bundled linear
evaluation uses the canonical `Rᵐᵒᵖ` character action; the older commutative-ring evaluation remains
available as a specialization.
-/

@[expose] public section

universe u v

/- Lemma 15.55.7 (Stacks `01DB`): the canonical evaluation map of any `R`-module into its double
character module is injective. -/
@[stacks 01DB "injectivity of character evaluation over a ring"]
#check fun (R : Type u) (M : Type v) [Ring R] [AddCommGroup M]
    [Module R M] ↦
  (CharacterModule.eval_injective (A := M))

/- The source-faithful arbitrary-ring evaluation is also bundled as a linear map and a monomorphism
in `ModuleCat R`. -/
@[stacks 01DB "bundled character evaluation over an arbitrary ring"]
#check @CharacterModule.opEvaluationLinear
#check @CharacterModule.opEvaluationApp
#check @CharacterModule.opEvaluationApp_injective
#check @CharacterModule.mono_opEvaluationApp

/- The commutative-ring linear form remains available for the symmetric specialization. -/
#check fun (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M]
    [Module R M] ↦
  CharacterModule.evalLinear_injective (R := R) (M := M)

/- Evaluation is also available as a natural transformation on bundled
modules. -/
#check @CharacterModule.evaluation
#check @CharacterModule.evaluation_app_injective
