/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.Algebra.Module.IdealPower.Quotient.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Evaluation of completed linear maps

A point in the adic completion of `Hom_R(M, N)` evaluates on a completed point of `M` by
evaluating at every ideal-power quotient stage and lifting the compatible values to the
completion of `N`.  This file owns that canonical map without Noetherian or finiteness
hypotheses; those hypotheses enter only when proving that the map is an isomorphism.
@stack 09BB
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace Ideal.PowerQuotient.Hom

variable {R : Type u} [CommRing R]

/-- The quotient-valued evaluation family associated to a completed linear map. -/
@[stacks 09BB "quotient evaluation family of a completed linear map"]
noncomputable def completedEvaluationFamily
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (z : AdicCompletion I (M →ₗ[R] N)) :
    (n : ℕ) → AdicCompletion I M →ₗ[R] Ideal.PowerQuotient I N n
  | 0 => 0
  | n + 1 =>
      (exactQuotientComparison I M N ⟨n + 1, Nat.succ_pos n⟩
        (AdicCompletion.eval I (M →ₗ[R] N) (n + 1) z)).comp
          (AdicCompletion.eval I M (n + 1))

/-- Quotient-valued completed evaluation commutes with every ideal-power transition. -/
@[stacks 09BB "compatibility of completed evaluation at quotient stages"]
theorem completedEvaluationFamily_compat
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (z : AdicCompletion I (M →ₗ[R] N)) {m n : ℕ} (hmn : m ≤ n) :
    (AdicCompletion.transitionMap I N hmn).comp
        (completedEvaluationFamily I M N z n) =
      completedEvaluationFamily I M N z m := by
  apply LinearMap.ext
  intro x
  cases m with
  | zero =>
      haveI : Subsingleton (Ideal.PowerQuotient I N 0) := by
        simp [Ideal.PowerQuotient]
      exact Subsingleton.elim _ _
  | succ m =>
      cases n with
      | zero => exact (Nat.not_succ_le_zero m hmn).elim
      | succ n =>
          have h (a b : ℕ+) (hab : (a : ℕ) ≤ (b : ℕ))
              (f : Ideal.PowerQuotient I (M →ₗ[R] N) (b : ℕ))
              (y : Ideal.PowerQuotient I M (b : ℕ)) :
              AdicCompletion.transitionMap I N hab (exactQuotientComparison I M N b f y) =
                exactQuotientComparison I M N a
                  (AdicCompletion.transitionMap I (M →ₗ[R] N) hab f)
                  (AdicCompletion.transitionMap I M hab y) := by
            refine Submodule.Quotient.induction_on _ f ?_
            intro f
            refine Submodule.Quotient.induction_on _ y ?_
            intro y
            rfl
          exact (h ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩ hmn
            (AdicCompletion.eval I (M →ₗ[R] N) (n + 1) z)
            (AdicCompletion.eval I M (n + 1) x)).trans
              (congrArg₂ (fun f y ↦
                exactQuotientComparison I M N ⟨m + 1, Nat.succ_pos m⟩ f y)
                (z.property hmn) (x.property hmn))

/-- Evaluation of a completed linear map, regarded first as an `R`-linear map. -/
@[stacks 09BB "underlying evaluation map for a completed linear map"]
noncomputable def completedEvaluationR
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (z : AdicCompletion I (M →ₗ[R] N)) :
    AdicCompletion I M →ₗ[R] AdicCompletion I N :=
  AdicCompletion.lift I (completedEvaluationFamily I M N z)
    (completedEvaluationFamily_compat I M N z)

/-- Completed evaluation commutes with scalars from the completed ring. -/
@[stacks 09BB "completion-linearity of completed evaluation"]
theorem completedEvaluationR_map_smul
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (z : AdicCompletion I (M →ₗ[R] N)) (r : AdicCompletion I R)
    (x : AdicCompletion I M) :
    completedEvaluationR I M N z (r • x) = r • completedEvaluationR I M N z x := by
  have h (n : ℕ+) (f : Ideal.PowerQuotient I (M →ₗ[R] N) (n : ℕ))
      (a : R ⧸ (I ^ (n : ℕ) • ⊤ : Ideal R)) (y : Ideal.PowerQuotient I M (n : ℕ)) :
      exactQuotientComparison I M N n f (a • y) =
        a • exactQuotientComparison I M N n f y := by
    refine Submodule.Quotient.induction_on _ a ?_
    intro a
    exact map_smul _ a _
  apply AdicCompletion.ext
  intro n
  change completedEvaluationFamily I M N z n (r • x) =
    AdicCompletion.eval I R n r • completedEvaluationFamily I M N z n x
  cases n with
  | zero =>
      haveI : Subsingleton (Ideal.PowerQuotient I N 0) := by
        simp [Ideal.PowerQuotient]
      exact Subsingleton.elim _ _
  | succ n =>
      exact h ⟨n + 1, Nat.succ_pos n⟩
        (AdicCompletion.eval I (M →ₗ[R] N) (n + 1) z)
        (AdicCompletion.eval I R (n + 1) r) (AdicCompletion.eval I M (n + 1) x)

/-- The completion-linear map induced by a completed `R`-linear map. -/
@[stacks 09BB "evaluation of a completed linear map"]
noncomputable def completedEvaluation
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (z : AdicCompletion I (M →ₗ[R] N)) :
    AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N where
  __ := completedEvaluationR I M N z
  map_smul' := completedEvaluationR_map_smul I M N z

/-- Completed evaluation is additive in the completed linear map. -/
@[stacks 09BB "additivity of completed linear-map evaluation"]
theorem completedEvaluation_add
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (z z' : AdicCompletion I (M →ₗ[R] N)) :
    completedEvaluation I M N (z + z') =
      completedEvaluation I M N z + completedEvaluation I M N z' := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  change completedEvaluationFamily I M N (z + z') n x =
    completedEvaluationFamily I M N z n x + completedEvaluationFamily I M N z' n x
  cases n with
  | zero => simp [completedEvaluationFamily]
  | succ n =>
      exact LinearMap.congr_fun
        (map_add (exactQuotientComparison I M N ⟨n + 1, Nat.succ_pos n⟩)
          (AdicCompletion.eval I (M →ₗ[R] N) (n + 1) z)
          (AdicCompletion.eval I (M →ₗ[R] N) (n + 1) z'))
        (AdicCompletion.eval I M (n + 1) x)

/-- Completed evaluation is linear over the completed base ring. -/
@[stacks 09BB "linearity of completed linear-map evaluation"]
theorem completedEvaluation_smul
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (r : AdicCompletion I R) (z : AdicCompletion I (M →ₗ[R] N)) :
    completedEvaluation I M N (r • z) = r • completedEvaluation I M N z := by
  have h (n : ℕ+) (a : R ⧸ (I ^ (n : ℕ) • ⊤ : Ideal R))
      (f : Ideal.PowerQuotient I (M →ₗ[R] N) (n : ℕ))
      (y : Ideal.PowerQuotient I M (n : ℕ)) :
      exactQuotientComparison I M N n (a • f) y =
        a • exactQuotientComparison I M N n f y := by
    refine Submodule.Quotient.induction_on _ a ?_
    intro a
    exact LinearMap.congr_fun (map_smul (exactQuotientComparison I M N n) a f) y
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  change completedEvaluationFamily I M N (r • z) n x =
    AdicCompletion.eval I R n r • completedEvaluationFamily I M N z n x
  cases n with
  | zero =>
      haveI : Subsingleton (Ideal.PowerQuotient I N 0) := by
        simp [Ideal.PowerQuotient]
      exact Subsingleton.elim _ _
  | succ n =>
      exact h ⟨n + 1, Nat.succ_pos n⟩ (AdicCompletion.eval I R (n + 1) r)
        (AdicCompletion.eval I (M →ₗ[R] N) (n + 1) z)
        (AdicCompletion.eval I M (n + 1) x)

/-- The canonical comparison from the completion of `Hom_R(M, N)` to completion-linear maps. -/
@[stacks 09BB "canonical completed Hom comparison"]
noncomputable def completedHomComparison
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    ModuleCat.of (AdicCompletion I R) (AdicCompletion I (M →ₗ[R] N)) ⟶
      ModuleCat.of (AdicCompletion I R)
        (AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N) :=
  ModuleCat.ofHom
    { toFun := completedEvaluation I M N
      map_add' := completedEvaluation_add I M N
      map_smul' := completedEvaluation_smul I M N }

/-- The completed Hom comparison sends a completed linear map to its completed evaluation. -/
@[simp, stacks 09BB "application of the completed Hom comparison"]
theorem completedHomComparison_apply
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (z : AdicCompletion I (M →ₗ[R] N)) :
    (completedHomComparison I M N).hom z = completedEvaluation I M N z := by
  rfl

/-- Evaluation modulo `I ^ (n + 1)` is the exact quotient-Hom comparison applied pointwise. -/
@[stacks 09BB "quotient formula for completed evaluation"]
theorem eval_completedEvaluation_succ
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (z : AdicCompletion I (M →ₗ[R] N)) (x : AdicCompletion I M) (n : ℕ) :
    AdicCompletion.eval I N (n + 1) (completedEvaluation I M N z x) =
      exactQuotientComparison I M N ⟨n + 1, Nat.succ_pos n⟩
        (AdicCompletion.eval I (M →ₗ[R] N) (n + 1) z)
          (AdicCompletion.eval I M (n + 1) x) := by
  rfl

/-- Completed evaluation extends ordinary evaluation on the canonical dense maps. -/
@[stacks 09BB "completed evaluation of ordinary elements"]
theorem completedEvaluation_of
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (x : M) :
    completedEvaluation I M N (AdicCompletion.of I (M →ₗ[R] N) f)
        (AdicCompletion.of I M x) =
      AdicCompletion.of I N (f x) := by
  apply AdicCompletion.ext
  intro n
  cases n with
  | zero =>
      haveI : Subsingleton (Ideal.PowerQuotient I N 0) := by
        simp [Ideal.PowerQuotient]
      exact Subsingleton.elim _ _
  | succ n => rfl

end Ideal.PowerQuotient.Hom
