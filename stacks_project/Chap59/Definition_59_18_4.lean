/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.FreeAbelianYoneda
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe u v w

variable {C : Type u} [Category.{v} C]
variable (G : Cᵒᵖ ⥤ Type w) (U : C)

/- Definition 59.18.4 (1): the free abelian presheaf on a presheaf of sets. -/
@[stacks 03OO] #check (CategoryTheory.FreeAbelianPresheaf.obj G : Cᵒᵖ ⥤ AddCommGrpCat.{w})

/- Definition 59.18.4 (2): objectwise, the free abelian presheaf is the free abelian group on
   each value of the presheaf. -/
@[stacks 03OO] #check (CategoryTheory.FreeAbelianPresheaf.obj_obj G (op U) :
  (FreeAbelianPresheaf.obj G).obj (op U) =
    AddCommGrpCat.of (FreeAbelianGroup (G.obj (op U))))

/- Definition 59.18.4 (3): the representable specialization, denoted Z_U in the source. -/
@[stacks 03OO] #check (CategoryTheory.FreeAbelianYoneda.obj U : Cᵒᵖ ⥤ AddCommGrpCat.{v})
