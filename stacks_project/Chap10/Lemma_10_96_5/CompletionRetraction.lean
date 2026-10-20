/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap10.Lemma_10_96_5.PositiveStageLimits
import StacksCheckRecall

/-!
# Lemma 10.96.5: completion retraction support

@stack 0318
-/

@[expose] public section

universe u

noncomputable section

open AdicCompletion
open CategoryTheory
open CategoryTheory.Limits

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.96.5: if `M^∧` is complete, then its adic completion retracts onto
`M^∧` by the universal property of completeness. -/
noncomputable abbrev positive_stage_completion_retraction
    (hcomplete : IsAdicComplete I (AdicCompletion I M)) :
    AdicCompletion I (AdicCompletion I M) →ₗ[R] AdicCompletion I M :=
  -- Local instance justification: `IsAdicComplete.lift` consumes the explicit completeness
  -- witness supplied by this source-facing construction; it is not ambient global data.
  letI : IsAdicComplete I (AdicCompletion I M) := hcomplete
  IsAdicComplete.lift I
    (fun n ↦ AdicCompletion.eval I (AdicCompletion I M) n)
    (fun {_ _} hmn ↦
      AdicCompletion.transitionMap_comp_eval I (AdicCompletion I M) hmn)

/-- Helper for Lemma 10.96.5: after identifying the positive-stage inverse limits with the two
adic completions, the inverse-limit right map is the completeness retraction from `(M^∧)^∧`
back to `M^∧`. -/
lemma positive_stage_limMap_stageMap_eq_completion_retraction
    (hcomplete : IsAdicComplete I (AdicCompletion I M)) :
    limMap (positive_stage_stageMap (R := R) (I := I) (M := M)) =
      (positive_stage_completion_system_limit_iso (R := R) (I := I) (M := M)).hom ≫
        ModuleCat.ofHom
          (positive_stage_completion_retraction (R := R) (I := I) (M := M) hcomplete) ≫
        (positive_stage_module_system_limit_iso (R := R) (I := I) (M := M)).inv := sorry

/-- Helper for Lemma 10.96.5: if `AdicCompletion I M` is complete, then the inverse limit of the
positive-stage kernel quotients `K_n / I ^ n M^∧` is zero. -/
lemma positive_stage_left_limit_isZero_of_complete
    (hcomplete : IsAdicComplete I (AdicCompletion I M)) :
    IsZero (limit (positive_stage_left_system (R := R) (I := I) (M := M))) := sorry

/- Completion-retraction support retained for the source-facing Lemma 10.96.5 statement. -/
@[stacks 0318 "completion evaluation compatibility"]
#check @AdicCompletion.transitionMap_comp_eval
@[stacks 0318 "completion retraction"]
#check @positive_stage_completion_retraction
@[stacks 0318 "limit map and stage map comparison"]
#check @positive_stage_limMap_stageMap_eq_completion_retraction
@[stacks 0318 "vanishing left limit under completeness"]
#check @positive_stage_left_limit_isZero_of_complete

/- The retraction's map is explicit, and its compatibility proof is supplied by the canonical
`AdicCompletion.transitionMap_comp_eval`; the data declaration therefore has no `sorryAx`. -/
#print axioms positive_stage_completion_retraction

end
