/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.Comparison
public import stacks_project.Chap90.Definition_90_21_1_Groupoid

/-!
# Groupoids in functors from groupoid-valued functors

A functor `C ⥤ Grpd` determines a groupoid in functors by taking objects, packaged
arrows, and the source, target, composition, identity, and inverse maps of the fibres.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]

#check (GroupoidInFunctors.ofFunctor :
  (C ⥤ Grpd.{w, w}) → GroupoidInFunctors.{u, v, w} C)

#check (GroupoidInFunctors.ofFunctor_U :
  ∀ F : C ⥤ Grpd.{w, w}, (GroupoidInFunctors.ofFunctor F).U = F ⋙ Grpd.objects)

#check (GroupoidInFunctors.ofFunctor_R_obj :
  ∀ (F : C ⥤ Grpd.{w, w}) (T : C),
    (GroupoidInFunctors.ofFunctor F).R.obj T = (Σ x : F.obj T, Σ y : F.obj T, (x ⟶ y)))

/- Reconstruction followed by evaluation preserves the object functor. -/
example (F : C ⥤ Grpd.{w, w}) :
    (GroupoidInFunctors.ofFunctor F).toFunctor ⋙ Grpd.objects = F ⋙ Grpd.objects := rfl
