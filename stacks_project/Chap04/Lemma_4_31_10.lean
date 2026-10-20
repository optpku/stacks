/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ForgetMiddle
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable (F : A ⥤ B) (G : C ⥤ B) (H : D ⥤ C)

/- Lemma 4.31.10 (Stacks 02XD): contracting the redundant middle object gives a canonical
equivalence `((π₂ F G) ⊡ H) ≌ F ⊡ (H ⋙ G)`. The reusable owner is
`CategoricalPullback.ForgetMiddle.equivalence`. -/
@[stacks 02XD]
#check (CategoryTheory.Limits.CategoricalPullback.ForgetMiddle.equivalence F G H :
  ((CategoricalPullback.π₂ F G) ⊡ H) ≌ (F ⊡ (H ⋙ G)))
