/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Characterizations of module torsion

This leaf records the elementwise formulations of torsion, torsion-freeness, and torsion modules
used throughout the Stacks Project.  The underlying data remain Mathlib's
`Submodule.torsion`, `Module.IsTorsionFree`, and `Module.IsTorsion`.

@stack 0536
-/

@[expose] public section

universe u v w

namespace Submodule

variable {R : Type u} {M : Type v}

/-- Lemma 15.22.2 (1): over a domain, the torsion submodule is the kernel of the
canonical map from `M` to its generic fiber `M ⊗[R] K`. -/
@[stacks 0537 "Lemma 15.22.2 (1): torsion as the generic-fiber kernel"]
theorem torsion_eq_ker_tensorFractionField {K : Type w}
    [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    torsion R M = LinearMap.ker ((TensorProduct.mk R M K).flip 1) := sorry

/-- Definition 15.22.1 (1): over a domain, membership in `torsion R M` is equivalent to
annihilation by a nonzero scalar. -/
@[stacks 0536 "Definition 15.22.1 (1): torsion elements"]
theorem mem_torsion_iff_exists_ne_zero_smul_eq_zero
    [CommSemiring R] [IsDomain R] [AddCommMonoid M] [Module R M] (x : M) :
    x ∈ torsion R M ↔ ∃ f : R, f ≠ 0 ∧ f • x = 0 := sorry
/- Proof strategy: rewrite with `Submodule.mem_torsion_iff`, then identify
`R⁰` with the nonzero scalars using `mem_nonZeroDivisors_iff_ne_zero`. -/

/-- Definition 15.22.1 (2): a module over a domain is torsion-free exactly when every element of
its torsion submodule is zero. -/
@[stacks 0536 "Definition 15.22.1 (2): torsion-free modules"]
theorem isTorsionFree_iff_forall_mem_torsion_eq_zero
    [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] :
    Module.IsTorsionFree R M ↔ ∀ x : M, x ∈ torsion R M → x = 0 := sorry
/- Proof strategy: combine `Submodule.isTorsionFree_iff_torsion_eq_bot` with
`Submodule.eq_bot_iff`. -/

end Submodule

namespace Module

variable {R : Type u} {M : Type v}

/-- Definition 15.22.1 (3): a module is torsion exactly when each of its elements belongs to the
canonical torsion submodule. -/
@[stacks 0536 "Definition 15.22.1 (3): torsion modules"]
theorem isTorsion_iff_forall_mem_torsion
    [CommSemiring R] [AddCommMonoid M] [Module R M] :
    IsTorsion R M ↔ ∀ x : M, x ∈ Submodule.torsion R M := sorry
/- Proof strategy: unfold `Module.IsTorsion` and rewrite each elementwise goal with
`Submodule.mem_torsion_iff`. -/

end Module
