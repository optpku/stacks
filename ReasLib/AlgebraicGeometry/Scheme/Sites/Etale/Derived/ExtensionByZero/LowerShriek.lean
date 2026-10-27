/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.ModuleExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Forget
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LocallyQuasiFinite

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.GrothendieckTopology CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section ExtensionIso

variable {U T : Scheme.{u}} (j : U ⟶ T) [Etale j] [LocallyQuasiFinite j]
  (Λ : Type u) [Ring Λ]
  [U.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [T.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
  [T.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]
  [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction j).op]
  [HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}]

/-- Extension by zero of module sheaves is additive. -/
instance extensionByZeroModule_additive :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).Additive := sorry

/-- Extension by zero of module sheaves preserves finite limits. -/
instance extensionByZeroModule_preservesFiniteLimits :
    PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ)) := sorry

/-- Extension by zero of module sheaves preserves finite colimits. -/
instance extensionByZeroModule_preservesFiniteColimits :
    PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ)) := sorry

/-- Exact extension by zero and exact finite-support shriek induce the derived
identification. -/
def extensionByZeroDerivedIsoLowerShriekModule
    [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ V : U.Etale, HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
 :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory ≅
      lowerShriekModuleDerived j Λ :=
  Functor.MapDerivedCategory.functorIso (lowerShriekModuleIsoExtensionByZero j Λ)

end ExtensionIso

end AlgebraicGeometry.Scheme.Etale

end
