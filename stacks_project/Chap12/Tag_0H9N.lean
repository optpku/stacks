/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Idempotents.Preadditive.Splitting
import StacksCheckRecall

@[expose] public section

open CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X : C} (f : X ⟶ X) (hf : f ≫ f = f)

/- Remark (0H9N). The idempotent and its complement annihilate one another. -/
@[stacks 0H9N] #check (CategoryTheory.Idempotents.comp_complement f hf :
  f ≫ (𝟙 X - f) = 0 ∧ (𝟙 X - f) ≫ f = 0)

/- The complement 𝟙 X - f is also idempotent. -/
#check (CategoryTheory.Idempotents.idem_of_id_sub_idem f hf :
  (𝟙 X - f) ≫ (𝟙 X - f) = 𝟙 X - f)
