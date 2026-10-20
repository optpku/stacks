/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelianYoneda.Injective
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.FreeAbelianYoneda.ULift

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
variable [HasWeakSheafify K AddCommGrpCat.{max u v}]

/- Lemma 19.7.3: extension from every abelian subsheaf of the free abelian sheaf represented by
an object of the site characterizes injective abelian sheaves. -/
@[stacks 01DO] #check
  fun (I : Sheaf K AddCommGrpCat.{max u v})
      (hI : HasSubobjectExtension K I) =>
    (injective_of_hasSubobjectExtension K I hI : Injective I)

#check @HasSubobjectExtension
#check @hasSubobjectExtension_of_injective
#check @injective_iff_hasSubobjectExtension
#check @CategoryTheory.GrothendieckTopology.FreeAbelianYoneda.ULift.obj
#check @CategoryTheory.GrothendieckTopology.FreeAbelianYoneda.ULift.homEquiv
