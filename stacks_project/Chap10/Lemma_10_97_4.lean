/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Filtration
import StacksCheckRecall

@[expose] public section

/-!
@stack 031C

# Filtration and quotient formulas for Noetherian completion
-/

noncomputable section

universe u v

namespace AdicCompletion

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

/- Lemma 10.97.4 (1): the `I`-adic completion of `M` is `I`-adically
complete. -/
@[stacks 031C "(1)"]
#check (isAdicComplete I.fg_of_isNoetherianRing :
  IsAdicComplete I (AdicCompletion I M))

/- Lemma 10.97.4 (2): the completion of `I ^ n M` is the `n`th
ideal-power submodule of the completion of `M`. -/
@[stacks 031C "(2)"]
#check (range_ofPowSMul_eq_pow_smul I M I.fg_of_isNoetherianRing :
  ∀ n : ℕ,
    (ofPowSMul I M n).range.restrictScalars R =
      I ^ n • (⊤ : Submodule R (AdicCompletion I M)))

/- Lemma 10.97.4 (3): reduction of the completion modulo `I ^ n` is
canonically reduction of `M` modulo `I ^ n`. -/
@[stacks 031C "(3)"]
#check quotientPowEquiv I M I.fg_of_isNoetherianRing

end AdicCompletion
