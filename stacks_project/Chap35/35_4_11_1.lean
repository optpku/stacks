/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.TensorHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- 35.4.11.1: for a commutative ring `R`, character duality gives a natural
isomorphism of contravariant bifunctors
`CharacterModule (M₁ ⊗[R] M₂) ≅ (M₁ →ₗ[R] CharacterModule M₂)`. -/
@[stacks 08WT] #check (CharacterModule.TensorHom.iso :
  ∀ (R : Type u) [CommRing R],
    CharacterModule.TensorHom.tensorFunctor R ≅
      CharacterModule.TensorHom.homFunctor R)
