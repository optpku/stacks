/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Finite rank of finite modules over a domain

Over a domain, a finite module has a well-defined natural-number rank, and that same rank appears
in the existence of maps to and from a finite free module with torsion kernel or cokernel, and in
principal localization to a free module.
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Over a domain, a finite module `M` admits an `R`-linear map into `Fin (finrank R M) → R`
whose kernel and cokernel are torsion modules. -/
theorem exists_linearMap_to_fin_fun_isTorsion_ker_coker :
    ∃ φ : M →ₗ[R] (Fin (finrank R M) → R),
      IsTorsion R (LinearMap.ker φ) ∧
        IsTorsion R ((Fin (finrank R M) → R) ⧸ LinearMap.range φ) := sorry

/-- Over a domain, a finite module becomes free of rank `finrank R M` after inverting a single
nonzero element. -/
theorem exists_nonzero_away_free_finrank_eq :
    ∃ f : R, f ≠ 0 ∧
      Free (Localization.Away f) (LocalizedModule.Away f M) ∧
        finrank (Localization.Away f) (LocalizedModule.Away f M) = finrank R M := sorry

/-- Over a domain, a finite module `M` admits an injective `R`-linear map from
`Fin (finrank R M) → R` whose cokernel is a torsion module. -/
theorem exists_injective_fin_fun_isTorsion_coker :
    ∃ ψ : (Fin (finrank R M) → R) →ₗ[R] M,
      Function.Injective ψ ∧ IsTorsion R (M ⧸ LinearMap.range ψ) := sorry

/-- A finite module over a domain has natural-number rank `r`, admits a map to `R^r` with
torsion kernel and cokernel, becomes free of rank `r` after inverting a nonzero element, and
admits an injective map from `R^r` with torsion cokernel. -/
theorem finite_module_rank :
    ∃ r : ℕ, (r : Cardinal) = Module.rank R M ∧
      (∃ φ : M →ₗ[R] (Fin r → R),
        IsTorsion R (LinearMap.ker φ) ∧
          IsTorsion R ((Fin r → R) ⧸ LinearMap.range φ)) ∧
      (∃ f : R, f ≠ 0 ∧
        Free (Localization.Away f) (LocalizedModule.Away f M) ∧
          finrank (Localization.Away f) (LocalizedModule.Away f M) = r) ∧
      (∃ ψ : (Fin r → R) →ₗ[R] M,
        Function.Injective ψ ∧ IsTorsion R (M ⧸ LinearMap.range ψ)) := by
  exact ⟨finrank R M, finrank_eq_rank R M,
    exists_linearMap_to_fin_fun_isTorsion_ker_coker,
    exists_nonzero_away_free_finrank_eq, exists_injective_fin_fun_isTorsion_coker⟩

end Module
