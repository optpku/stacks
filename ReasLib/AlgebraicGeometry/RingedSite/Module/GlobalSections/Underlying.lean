/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Underlying

/-!
# Underlying additive sections of module sheaves

The additive sections of a module sheaf are obtained by evaluating the module sheaf
and then forgetting the scalar action.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleSections

variable (X : RingedSite.{u, v, w})

namespace Underlying

/-- The sections over `U`, after forgetting module structure, valued in additive groups. -/
@[stacks 0D6J "underlying additive sections"]
abbrev sections (U : X) :
    RingedSite.ModuleCat.{z} X ⥤ AddCommGrpCat.{z} :=
  underlyingAbelianSheafFunctor.{z} X ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{z} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{z}).obj (op U)

end Underlying

/-- The forgetful functor from modules over the section ring to additive groups. -/
@[stacks 0D6J "section-module forgetful functor"]
abbrev sectionForget (U : X) :
    _root_.ModuleCat.{z} (X.structureSheaf.1.obj (op U)) ⥤
      AddCommGrpCat.{z} :=
  forget₂ (_root_.ModuleCat.{z} (X.structureSheaf.1.obj (op U)))
    AddCommGrpCat.{z}

namespace Underlying

/-- The underived sections functor is identified with evaluation followed by forgetting
scalars. -/
@[stacks 0D6J "objectwise sections underlying bridge"]
noncomputable def sectionsForgetIso (U : X) :
    sections X U ≅
      SheafOfModules.evaluation.{z} X.structureSheaf (op U) ⋙
        sectionForget.{z} X U :=
  Functor.isoWhiskerRight
    (SheafOfModules.toSheafCompSheafToPresheafIso X.structureSheaf)
    ((evaluation X.carrierᵒᵖ AddCommGrpCat.{z}).obj (op U))

end Underlying

end RingedSite.Hom.ModuleSections
