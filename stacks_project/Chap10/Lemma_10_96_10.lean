/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Completeness.Submodule
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.96.10
@stack 031A
-/

universe u v

section

open AdicCompletion Submodule

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (K : Submodule R M)

/- Lemma 10.96.10: if `M` is `I`-adically complete, then a submodule `K` is the intersection
of the submodules `K + I ^ n M` if and only if the quotient module `M ⧸ K` is `I`-adically
complete. -/
variable [IsAdicComplete I M]

@[stacks 031A "source orientation"]
#check show
    K = ⨅ n : ℕ, K ⊔ I ^ n • (⊤ : Submodule R M) ↔ IsAdicComplete I (M ⧸ K)
  from (K.isAdicComplete_quotient_iff I).symm

@[stacks 031A "precomplete quotient"]
#check @IsPrecomplete.quotient

@[stacks 031A "precompleteness under surjections"]
#check @IsPrecomplete.of_surjective

@[stacks 031A "Hausdorff quotient criterion"]
#check @Submodule.isHausdorff_quotient_iff

@[stacks 031A "adic-complete quotient criterion"]
#check @Submodule.isAdicComplete_quotient_iff

end
