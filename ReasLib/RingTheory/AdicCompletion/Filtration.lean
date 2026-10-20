/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The ideal-power filtration on an adic completion

This file identifies the completed ideal-power submodule inside an adic
completion and exposes the resulting finite-stage quotient equivalence.  The
finitely generated ideal hypothesis is explicit, so the API applies beyond
Noetherian base rings.
-/

@[expose] public section

noncomputable section

universe u v

namespace AdicCompletion

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The image of the completion of `I ^ n M` is the `n`th ideal-power
submodule of the completion of `M`. -/
@[stacks 031C "(2)"]
theorem range_ofPowSMul_eq_pow_smul (hI : I.FG) (n : ℕ) :
    (ofPowSMul I M n).range.restrictScalars R =
      I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := sorry

/-- The `n`th quotient of an adic completion is canonically the `n`th
quotient of the original module. -/
@[stacks 031C "(3)"]
noncomputable def quotientPowEquiv (hI : I.FG) (n : ℕ) :
    ((AdicCompletion I M) ⧸
        (I ^ n • (⊤ : Submodule R (AdicCompletion I M)))) ≃ₗ[R]
      M ⧸ (I ^ n • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _ (pow_smul_top_eq_ker_eval hI)).trans
    ((eval I M n).quotKerEquivOfSurjective (eval_surjective I M n))

/-- The finite-stage quotient equivalence is induced by evaluation. -/
@[simp, stacks 031C "finite-stage quotient evaluation"]
theorem quotientPowEquiv_mk (hI : I.FG) (n : ℕ) (x : AdicCompletion I M) :
    quotientPowEquiv I M hI n (Submodule.Quotient.mk x) = eval I M n x := sorry

/-- The inverse finite-stage quotient equivalence is induced by the dense
map from the original module to its completion. -/
@[simp, stacks 031C "finite-stage quotient inverse"]
theorem quotientPowEquiv_symm_mk (hI : I.FG) (n : ℕ) (x : M) :
    (quotientPowEquiv I M hI n).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (of I M x) := sorry

end AdicCompletion
