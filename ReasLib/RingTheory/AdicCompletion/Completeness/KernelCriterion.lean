module

public import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel criterion for completeness of an adic completion

@stack 0318
-/

@[expose] public section

universe u v

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- Lemma 10.96.5: the adic completion of `M` is complete exactly when every
positive-stage evaluation kernel is the corresponding ideal-power multiple. -/
@[stacks 0318]
theorem isAdicComplete_iff_ker_eval_eq_pow_smul_top
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    IsAdicComplete I (AdicCompletion I M) ↔
      ∀ n : ℕ+,
        (eval I M (n : ℕ)).ker =
          I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)) := sorry

end AdicCompletion
