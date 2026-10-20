/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map.CospanTransform
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {Z : Type u₃} [Category.{v₃} Z]
variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {C : Type u₆} [Category.{v₆} C]
variable {H : X ⥤ Z} {I : Y ⥤ Z} {L : X ⥤ A} {K : Y ⥤ B}
variable {M : Z ⥤ C} {F : A ⥤ C} {G : B ⥤ C}
variable (squareLeft : H ⋙ M ≅ L ⋙ F) (squareRight : I ⋙ M ≅ K ⋙ G)

/- Lemma 4.31.6: invertible comparison cells on the two faces of a vertical cospan diagram
determine a `CatCospanTransform`; applying `CategoricalPullback.map` gives the induced functor on
the two categorical pullbacks. The canonical reusable constructor is
`CatCospanTransform.ofIso`. -/
@[stacks 02XA]
#check (CategoricalPullback.map (CatCospanTransform.ofIso squareLeft squareRight) :
  H ⊡ I ⥤ F ⊡ G)
