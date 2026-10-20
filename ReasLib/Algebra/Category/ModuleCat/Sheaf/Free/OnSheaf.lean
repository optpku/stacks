/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Free module sheaves on type-valued sheaves

This file globalizes the pointwise free-module construction: forget a type-valued sheaf to its
presheaf, form the pointwise free module presheaf, and sheafify.  Keeping these three canonical
functors visible makes the construction usable for graded and differential graded generators.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{w})
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The pointwise free `R`-module presheaf on a type-valued sheaf, before sheafification. -/
noncomputable abbrev freePresheafOnSheaf (S : Sheaf J (Type w)) :
    PresheafOfModules.{w} R.obj :=
  (PresheafOfModules.free R.obj).obj S.obj

/-- The free `R`-module sheaf generated locally by a type-valued sheaf. -/
@[stacks 0FSF "free module sheaf on a sheaf of generators"]
noncomputable def freeOnSheaf : Sheaf J (Type w) ⥤ SheafOfModules.{w} R :=
  sheafToPresheaf J (Type w) ⋙
    PresheafOfModules.free R.obj ⋙
      PresheafOfModules.sheafification (𝟙 R.obj)

/-- Before sheafification, the sections over `U` form the free `R(U)`-module on `S(U)`. -/
theorem freePresheafOnSheaf_obj (S : Sheaf J (Type w)) (U : Cᵒᵖ) :
    (freePresheafOnSheaf R S).obj U =
      (ModuleCat.free (R.obj.obj U)).obj (S.obj.obj U) := sorry

/-- The free module sheaf on `S` is the sheafification of its pointwise free module presheaf. -/
theorem freeOnSheaf_obj (S : Sheaf J (Type w)) :
    (freeOnSheaf R).obj S =
      (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        (freePresheafOnSheaf R S) := sorry

/-- The free-on-sheaf functor maps a morphism by the pointwise free map followed by
sheafification. -/
theorem freeOnSheaf_map {S T : Sheaf J (Type w)} (f : S ⟶ T) :
    (freeOnSheaf R).map f =
      (PresheafOfModules.sheafification (𝟙 R.obj)).map
        ((PresheafOfModules.free R.obj).map
          ((sheafToPresheaf J (Type w)).map f)) := sorry

end SheafOfModules

end
