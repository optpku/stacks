/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Characterization of the snake connecting morphism

The canonical pullback-pushout square uniquely determines the connecting morphism of a snake
input.  This file exposes that uniqueness as a rewrite-friendly specification.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.ShortComplex.SnakeInput

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- 010H (Lemma 12.5.17 (1)): a morphism is the snake connecting morphism exactly when it makes
the canonical pullback-pushout square commute. -/
@[stacks 010H]
theorem eq_δ_iff (S : SnakeInput C) (d : S.L₀.X₃ ⟶ S.L₃.X₁) :
    d = S.δ ↔
      (pullback.snd S.L₁.g S.v₀₁.τ₃ : S.P ⟶ S.L₀.X₃) ≫ d ≫
          (pushout.inr S.L₂.f S.v₂₃.τ₁ : S.L₃.X₁ ⟶ S.P') =
        (pullback.fst S.L₁.g S.v₀₁.τ₃ : S.P ⟶ S.L₁.X₂) ≫ S.v₁₂.τ₂ ≫
          (pushout.inl S.L₂.f S.v₂₃.τ₁ : S.L₂.X₂ ⟶ S.P') := sorry

/-- A morphism satisfying the characteristic pullback-pushout square is the snake connecting
morphism. -/
theorem eq_δ_of_snd_comp_inr (S : SnakeInput C) (d : S.L₀.X₃ ⟶ S.L₃.X₁)
    (hd :
      (pullback.snd S.L₁.g S.v₀₁.τ₃ : S.P ⟶ S.L₀.X₃) ≫ d ≫
          (pushout.inr S.L₂.f S.v₂₃.τ₁ : S.L₃.X₁ ⟶ S.P') =
        (pullback.fst S.L₁.g S.v₀₁.τ₃ : S.P ⟶ S.L₁.X₂) ≫ S.v₁₂.τ₂ ≫
          (pushout.inl S.L₂.f S.v₂₃.τ₁ : S.L₂.X₂ ⟶ S.P')) :
    d = S.δ := sorry

end CategoryTheory.ShortComplex.SnakeInput

