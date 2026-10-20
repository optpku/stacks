/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite torsion-free modules and finite free embeddings

This leaf keeps the source-faithful finite-free model `Fin n → R` as the existential conclusion;
the finite module and torsion-free predicate remain Mathlib's canonical owners.

@stack 0AUU
-/

@[expose] public section

universe u v

namespace Module.IsTorsionFree

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Lemma 15.22.7 (0AUU): a finite module over a domain is torsion-free exactly when it admits an
injective linear map into a finite free module `Fin n → R`. -/
@[stacks 0AUU "finite torsion-free modules embed in finite free modules"]
theorem iff_exists_injective_fin_fun :
    IsTorsionFree R M ↔
      ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R), Function.Injective f := sorry
-- Proof strategy: use `Module.Finite.exists_fin'`, `Module.finBasis`,
-- `LinearIndependent.iff_fractionRing`, and the localization numerator API to clear denominators
-- in the forward implication; for the reverse implication use
-- `Function.Injective.moduleIsTorsionFree` on the canonical finite free target.

end Module.IsTorsionFree
