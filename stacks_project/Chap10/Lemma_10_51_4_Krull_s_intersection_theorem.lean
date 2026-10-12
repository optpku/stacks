/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Filtration
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.51.4 (Krull's intersection theorem)

@stack 00IP
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {M : Type v}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]

/- Lemma 10.51.4 (Krull's intersection theorem): let `R` be a Noetherian local ring, let `I` be
a proper ideal of `R`, and let `M` be a finite `R`-module. Then
`⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) = ⊥`. This is the canonical mathlib theorem
`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`. -/
@[stacks 00IP]
#check @Ideal.iInf_pow_smul_eq_bot_of_isLocalRing

end
