/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sections after localization at a sheaf

This leaf owns the reusable sections functor obtained by restricting module sheaves to the
category-of-elements localization at a set-valued sheaf and then taking global sections there.
It also exposes the induced functor from the homotopy category to the derived category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf ComplexShape

noncomputable section

universe uX vX

namespace RingedSite.Localization.AtSheaf

/-- Additive sections of module sheaves after localization at a set-valued sheaf. -/
@[stacks 0731 "sections functor"]
abbrev moduleSections (X : RingedSite.{uX, vX, max uX vX})
    (F : Sheaf X.siteTopology (Type vX))
    [HasWeakSheafify (site X.structureSheaf F).siteTopology AddCommGrpCat.{max uX vX}]
    [HasGlobalSectionsFunctor (site X.structureSheaf F).siteTopology
      AddCommGrpCat.{max uX vX}] :
    SheafOfModules X.structureSheaf ⥤ AddCommGrpCat.{max uX vX} :=
  SheafOfModules.Localization.AtSheaf.restriction X.structureSheaf F ⋙
    RingedSite.Hom.moduleGlobalSectionsAdditiveFunctor (site X.structureSheaf F)

/-- Sections after localization at a sheaf form an additive functor. -/
@[stacks 0731 "additivity"]
instance (priority := 1100) moduleSections_additive
    (X : RingedSite.{uX, vX, max uX vX}) (F : Sheaf X.siteTopology (Type vX))
    [HasWeakSheafify (site X.structureSheaf F).siteTopology AddCommGrpCat.{max uX vX}]
    [HasGlobalSectionsFunctor (site X.structureSheaf F).siteTopology
      AddCommGrpCat.{max uX vX}] :
    (moduleSections X F).Additive := sorry

/-- The homotopy-to-derived functor induced by sections after localization at a sheaf. -/
@[stacks 0731 "homotopy-to-derived functor"]
abbrev moduleSectionsToDerived (X : RingedSite.{uX, vX, max uX vX})
    (F : Sheaf X.siteTopology (Type vX))
    [HasWeakSheafify (site X.structureSheaf F).siteTopology AddCommGrpCat.{max uX vX}]
    [HasGlobalSectionsFunctor (site X.structureSheaf F).siteTopology
      AddCommGrpCat.{max uX vX}] :
    HomotopyCategory (SheafOfModules X.structureSheaf) (up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{max uX vX} :=
  Functor.Homotopy.toDerived (moduleSections X F)

section InstanceCheck

variable (X : RingedSite.{uX, vX, max uX vX}) (F : Sheaf X.siteTopology (Type vX))
variable [HasWeakSheafify (site X.structureSheaf F).siteTopology AddCommGrpCat.{max uX vX}]
variable [HasGlobalSectionsFunctor (site X.structureSheaf F).siteTopology
  AddCommGrpCat.{max uX vX}]

#synth (moduleSections X F).Additive

end InstanceCheck

end RingedSite.Localization.AtSheaf
