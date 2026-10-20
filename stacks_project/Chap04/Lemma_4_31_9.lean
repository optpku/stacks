/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.OuterProjection
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]
variable {T : Type u₆} [Category.{v₆} T]
variable (AB : A ⥤ B) (ED : E ⥤ D)
variable {CB : C ⥤ B} {CD : C ⥤ D} {BT : B ⥤ T} {DT : D ⥤ T}
variable (hcomm : CB ⋙ BT = CD ⋙ DT)

/- Lemma 4.31.9: a strictly commuting diagram of two composable cospans has a canonical functor
from the iterated `2`-fibre product to the `2`-fibre product of its outer entries. -/
@[stacks 04S7]
#check (CategoryTheory.Limits.CategoricalPullback.OuterProjection.ofEq AB ED hcomm :
  ((CategoricalPullback.π₂ AB CB ⋙ CD) ⊡ ED) ⥤
    ((AB ⋙ BT) ⊡ (ED ⋙ DT)))
