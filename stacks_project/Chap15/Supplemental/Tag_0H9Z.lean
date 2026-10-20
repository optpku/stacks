/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.Dimension.FiniteRank
public import ReasLib.LinearAlgebra.Dimension.FractionRing

/-!
# Finite rank of a finite module over a domain
-/

@[expose] public section

open scoped Cardinal TensorProduct

universe u v

/- Lemma [Stacks 0H9Z] -/
@[stacks 0H9Z]
#check (Module.finite_module_rank :
  ∀ {R : Type u} {M : Type v} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M],
    ∃ r : ℕ, (r : Cardinal) = Module.rank R M ∧
      (∃ φ : M →ₗ[R] (Fin r → R),
        Module.IsTorsion R (LinearMap.ker φ) ∧
          Module.IsTorsion R ((Fin r → R) ⧸ LinearMap.range φ)) ∧
      (∃ f : R, f ≠ 0 ∧
        Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
          Module.finrank (Localization.Away f) (LocalizedModule.Away f M) = r) ∧
      (∃ ψ : (Fin r → R) →ₗ[R] M,
        Function.Injective ψ ∧ Module.IsTorsion R (M ⧸ LinearMap.range ψ)))

#check (Module.finrank_fractionRing_tensor :
  ∀ (R : Type u) [CommRing R] [IsDomain R] (M : Type v)
    [AddCommGroup M] [Module R M],
    Module.finrank (FractionRing R) (FractionRing R ⊗[R] M) = Module.finrank R M)
