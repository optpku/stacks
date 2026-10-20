/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.BilinearForm.AdjointCoker
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 55.2.5 -/
@[stacks 0C6W] #check (LinearMap.torsionCokerAdjointCompEquiv :
  ∀ (L₀ : Type u) [AddCommGroup L₀] [Module.Finite ℤ L₀] [Module.Free ℤ L₀]
    (L₁ : Type v) [AddCommGroup L₁] [Module.Finite ℤ L₁] [Module.Free ℤ L₁]
    (B₀ : LinearMap.BilinForm ℤ L₀) (B₁ : LinearMap.BilinForm ℤ L₁)
    [LinearMap.IsPerfPair B₀]
    (h₀_symm : B₀.IsSymm) (h₀_pos : ∀ x : L₀, x ≠ 0 → 0 < B₀ x x)
    (h₁_symm : B₁.IsSymm) (h₁_pos : ∀ x : L₁, x ≠ 0 → 0 < B₁ x x)
    (d : L₀ →ₗ[ℤ] L₁) (dStar : L₁ →ₗ[ℤ] L₀)
    (h_adjoint : LinearMap.IsAdjointPair B₀ B₁ d dStar),
    Nonempty
      (AddCommGroup.torsion (L₀ ⧸ (dStar.comp d).range) ≃+
        Module.Dual ℤ d.range ⧸ (B₁.flip.restrict d.range).range))
