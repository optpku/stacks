/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.SnakeLemma
import StacksCheckRecall

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : ShortComplex.SnakeInput C)

/- Lemma 12.5.17 (1): the characteristic pullback-pushout square uniquely determines the
connecting morphism. -/
@[stacks 010H] #check S.eq_δ_iff

/- A snake input has a canonical connecting morphism from the third
kernel object to the first cokernel object. -/
#check
  (S.δ : S.L₀.X₃ ⟶ S.L₃.X₁)

/- Lemma 12.5.17 (2): the connecting morphism satisfies the canonical pullback-pushout
square from the source statement. -/
#check
  (S.snd_δ_inr :
    (pullback.snd S.L₁.g S.v₀₁.τ₃ : S.P ⟶ S.L₀.X₃) ≫ S.δ ≫
        (pushout.inr S.L₂.f S.v₂₃.τ₁ : S.L₃.X₁ ⟶ S.P') =
      (pullback.fst S.L₁.g S.v₀₁.τ₃ : S.P ⟶ S.L₁.X₂) ≫ S.v₁₂.τ₂ ≫
        (pushout.inl S.L₂.f S.v₂₃.τ₁ : S.L₂.X₂ ⟶ S.P'))

/- Lemma 12.5.17 (3): the induced six-term kernel-connecting-cokernel sequence is exact. -/
#check (S.snake_lemma : S.composableArrows.Exact)

section LeftEndpoint

variable [Mono S.L₁.f]

/- Lemma 12.5.17 (4): a monic first map in the upper row induces a monic first map on
kernels. -/
#check (ShortComplex.SnakeInput.mono_L₀_f (S := S) : Mono S.L₀.f)

end LeftEndpoint

section RightEndpoint

variable [Epi S.L₂.g]

/- Lemma 12.5.17 (5): an epic last map in the lower row induces an epic last map on
cokernels. -/
#check (ShortComplex.SnakeInput.epi_L₃_g (S := S) : Epi S.L₃.g)

end RightEndpoint

end CategoryTheory
