/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
import StacksCheckRecall

/-!
# Definition 18.43.1 finite compatibility entry point

Finite local constancy is specialized from `Sheaf.IsLocallyConstantWith` for
set-valued and group-valued sheaves.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Types

variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]
variable (F : Sheaf J (Type w))

/- Definition 18.43.1 (3): a set-valued sheaf is finite locally constant when its local
constant models are finite sets. -/
@[stacks 093Q "(3)"]
#check (IsFiniteLocallyConstant F : Prop)

end Types

section Groups

variable [HasWeakSheafify J GrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) GrpCat.{w}]
variable (G : Sheaf J GrpCat.{w})

/- Definition 18.43.1 (4): a group-valued sheaf is finite locally constant when its local
constant models are finite groups. -/
@[stacks 093Q "(4)"]
#check (IsFiniteLocallyConstantGrp G : Prop)

end Groups

end CategoryTheory.Sheaf
