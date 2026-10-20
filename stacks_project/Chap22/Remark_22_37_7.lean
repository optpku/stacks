/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Functor.ConeComparison
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe vC uC vD uD

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [HasZeroObject C] [HasZeroObject D]
variable [Preadditive C] [Preadditive D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor C n).Additive]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable [Pretriangulated C] [Pretriangulated D]
variable {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
variable [F.IsTriangulated] [G.IsTriangulated]
variable (P : ObjectProperty C) (e : P.ι ⋙ F ≅ P.ι ⋙ G)
variable {Z : C} (hZ : P.coneOfMap Z)

/- Remark 22.37.7 (09SB): a natural comparison between two triangulated functors on the full
subcategory of graded-projective differential graded modules induces an isomorphism on every
object that is a cone of a morphism between such modules. -/
@[stacks 09SB] #check
  (CategoryTheory.Functor.ConeComparison.nonempty_objIso P e hZ :
    Nonempty (F.obj Z ≅ G.obj Z))

#check @CategoryTheory.Functor.ConeComparison.coneIso
