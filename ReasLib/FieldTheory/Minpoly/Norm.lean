/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open Module
open IntermediateField
open scoped IntermediateField

universe u v

namespace Algebra

variable (K : Type u) {L : Type v}
variable [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Lemma 9.20.3 (Tag 0BIH): in a finite field extension, the norm of `α` is the constant
coefficient of `minpoly K α`, raised to the degree over `K⟮α⟯`, with the standard sign. -/
theorem norm_eq_sign_mul_minpoly_coeff_zero_pow_finrank_adjoin
    (α : L) : norm K α = (-1 : K) ^ finrank K L * (minpoly K α).coeff 0 ^ finrank K⟮α⟯ L := by
  have hα : IsIntegral K α := .of_finite K α
  rw [norm_eq_norm_adjoin K α]
  have hgen : norm K (AdjoinSimple.gen K α) =
      (-1 : K) ^ finrank K K⟮α⟯ * (minpoly K α).coeff 0 := by
    simpa [IntermediateField.adjoin.powerBasis_gen hα, minpoly_gen K α,
      IntermediateField.adjoin.finrank hα] using
      (PowerBasis.norm_gen_eq_coeff_zero_minpoly
        (IntermediateField.adjoin.powerBasis hα : PowerBasis K K⟮α⟯))
  rw [hgen, mul_pow, ← pow_mul]
  congr 1
  rw [finrank_mul_finrank K K⟮α⟯ L]

end Algebra
