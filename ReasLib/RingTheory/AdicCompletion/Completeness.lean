/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Retracts of Adically Complete Modules

This leaf records the categorical stability of adic completeness under an
explicit split linear retract.  The splitting is kept as ordinary linear data,
so it does not introduce a noncanonical global instance.
-/

@[expose] public section

universe u v

namespace IsAdicComplete

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type v} [AddCommGroup N] [Module R N]

/-- An explicit linear retract of an `I`-adically complete module is
`I`-adically complete. -/
theorem of_linear_retract
    (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (h_retract : g.comp f = LinearMap.id)
    (h_complete : IsAdicComplete I N) :
    IsAdicComplete I M := sorry

end IsAdicComplete
