/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering

@[expose] public section

universe v u r w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (R : Type r) [Ring R]

/-- Forgetting the module structure preserves the sheaf condition on any site when the ring is
small in the module universe, so its regular module can detect sections. -/
instance (priority := 11000) GrothendieckTopology.moduleCatForget_hasSheafCompose
    [Small.{w} R] :
    J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) := sorry

/-- The functor taking a sheaf of modules to its underlying sheaf of abelian groups.
The optional preservation proof is synthesized after the module universe is inferred. -/
def moduleSheafToAddCommGrp
    (h : J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) := by infer_instance) :
    Sheaf J (ModuleCat.{w} R) ⥤ Sheaf J AddCommGrpCat.{w} :=
  letI := h
  sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})

/-- The presheaf underlying the abelian sheaf of a module sheaf is obtained by
composition with the forgetful functor. -/
theorem moduleSheafToAddCommGrp_obj_obj
    [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]
    (P : Sheaf J (ModuleCat.{w} R)) :
    ((moduleSheafToAddCommGrp J R).obj P).obj =
      P.obj ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} := rfl

end CategoryTheory
