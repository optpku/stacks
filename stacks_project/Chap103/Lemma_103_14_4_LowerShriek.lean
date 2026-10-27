/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.ModuleLowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import stacks_project.Chap103.Lemma_103_14_2_Ringed
public import stacks_project.Chap103.Lemma_103_14_2_Topos

/-!
# Module lower shriek along lisse-étale and flat-fppf inclusions

Restriction of modules along the lisse-étale and flat-fppf inclusions of an
algebraic stack admits a left adjoint, the specialization of the continuous and
cocontinuous module lower shriek. The forgetful mate compares this adjoint with
abelian lower shriek, and the unit encodes `g^* g_! = id`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open RingedSite.Cocontinuous

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleInverseImage :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    SheafOfModules.{u} (etaleStructureSheaf X) ⥤
      SheafOfModules.{u} (lisseEtaleStructureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriek :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    SheafOfModules.{u} (lisseEtaleStructureSheaf X) ⥤
      SheafOfModules.{u} (etaleStructureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriek.adjunction :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    lisseEtaleModuleLowerShriek X ⊣ lisseEtaleModuleInverseImage X)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriek.homEquiv :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    (F : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    (G : SheafOfModules.{u} (etaleStructureSheaf X)),
    ((lisseEtaleModuleLowerShriek X).obj F ⟶ G) ≃
      (F ⟶ (lisseEtaleModuleInverseImage X).obj G))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriek.underlyingComparison :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (lisseEtaleInclusion X).op.HasLeftKanExtension P],
    SheafOfModules.toSheaf.{u} (lisseEtaleStructureSheaf X) ⋙
        lisseEtaleAbelianLowerShriek X ⟶
      lisseEtaleModuleLowerShriek X ⋙
        SheafOfModules.toSheaf.{u} (etaleStructureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriek.underlyingComparison_isIso :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (lisseEtaleInclusion X).op.HasLeftKanExtension P],
    IsIso (lisseEtaleModuleLowerShriek.underlyingComparison X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriek_unit_app_isIso :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X] (F : SheafOfModules.{u} (lisseEtaleStructureSheaf X)),
    IsIso ((lisseEtaleModuleLowerShriek.adjunction X).unit.app F))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfModuleInverseImage :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    SheafOfModules.{u} (structureSheaf X) ⥤
      SheafOfModules.{u} (flatFppfStructureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriek :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    SheafOfModules.{u} (flatFppfStructureSheaf X) ⥤
      SheafOfModules.{u} (structureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriek.adjunction :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    flatFppfModuleLowerShriek X ⊣ flatFppfModuleInverseImage X)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriek.homEquiv :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    (F : SheafOfModules.{u} (flatFppfStructureSheaf X))
    (G : SheafOfModules.{u} (structureSheaf X)),
    ((flatFppfModuleLowerShriek X).obj F ⟶ G) ≃
      (F ⟶ (flatFppfModuleInverseImage X).obj G))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriek.underlyingComparison :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u}]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (flatFppfInclusion X).op.HasLeftKanExtension P],
    SheafOfModules.toSheaf.{u} (flatFppfStructureSheaf X) ⋙
        flatFppfAbelianLowerShriek X ⟶
      flatFppfModuleLowerShriek X ⋙
        SheafOfModules.toSheaf.{u} (structureSheaf X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriek.underlyingComparison_isIso :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u}]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (flatFppfInclusion X).op.HasLeftKanExtension P],
    IsIso (flatFppfModuleLowerShriek.underlyingComparison X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriek_unit_app_isIso :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X] (F : SheafOfModules.{u} (flatFppfStructureSheaf X)),
    IsIso ((flatFppfModuleLowerShriek.adjunction X).unit.app F))

end AlgebraicGeometry.AlgebraicStack
