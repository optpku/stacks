/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
@stack 031D
# Hausdorff adic modules

This leaf owns the converse of Mathlib's intersection formula for adic
Hausdorffness. The proposition is independent of finite generation and
completeness, so finite-module and derived-completeness entries can reuse it
without a chapter dependency.
-/

universe u v

section

open scoped BigOperators

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace IsHausdorff

/-- Lemma 10.96.12 / Proposition 15.92.5 (Stacks 031D): vanishing of the
adic intersection gives the canonical `IsHausdorff` structure. -/
@[stacks 031D "intersection criterion for adic Hausdorffness"]
theorem of_iInf_pow_smul_eq_bot
    {I : Ideal R}
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥) :
    IsHausdorff I M := sorry

/-- An `I`-adic Hausdorff module induces an `I`-adic Hausdorff structure on
each of its submodules. -/
@[stacks 031D "Hausdorffness descends to submodules"]
theorem submodule {I : Ideal R} (N : Submodule R M) [IsHausdorff I M] :
    IsHausdorff I N := sorry

end IsHausdorff

end
