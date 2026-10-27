/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.CategoryTheory.Localization.Triangulated
import ReasLib.CategoryTheory.Functor.Derived.Total.EverywhereDefined
import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
import StacksCheckRecall

@[expose] public section

/-!
# Equation 13.14.9.1 (05SW)

When the source-derived functor is everywhere defined, its canonical total
model is a functor from the localization to the original target category.
Right and left source-definedness are independent alternatives.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  [Limits.HasZeroObject 𝒟] [Limits.HasZeroObject 𝒟']
  [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ]
  [Preadditive 𝒟] [Preadditive 𝒟']
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
  [∀ n : ℤ, (shiftFunctor 𝒟' n).Additive]
  [Pretriangulated 𝒟] [Pretriangulated 𝒟']
  [IsTriangulated 𝒟] [IsTriangulated 𝒟']
  (S : MorphismProperty 𝒟) (F : 𝒟 ⥤ 𝒟')
  [F.CommShift ℤ] [F.IsTriangulated]
  [MorphismProperty.IsSaturatedMultiplicativeSystem S]
  [S.IsCompatibleWithTriangulation]

section Right

variable [Functor.RightDerived.EverywhereDefined F S]

/- 13.14.9.1 (1): the everywhere defined right-derived functor. -/
@[stacks 05SW] #check
  (CategoryTheory.Functor.RightDerived.EverywhereDefined.functor F S S.Q : S.Localization ⥤ 𝒟')

end Right

section Left

variable [Functor.LeftDerived.EverywhereDefined F S]

/- 13.14.9.1 (2): the everywhere defined left-derived functor. -/
@[stacks 05SW] #check
  (CategoryTheory.Functor.LeftDerived.EverywhereDefined.functor F S S.Q : S.Localization ⥤ 𝒟')

end Left

end CategoryTheory
