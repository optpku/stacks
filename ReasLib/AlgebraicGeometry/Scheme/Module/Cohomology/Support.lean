/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.SectionsWithSupport
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Support

variable {X : Scheme.{u}}

/-- Taking the ambient subsheaf of sections supported on a closed subset is additive. -/
instance ambientFunctor_additive (Z : Closeds X) :
    (SheafOfModules.ClosedSubset.SectionsWithSupport.ambientFunctor X.ringCatSheaf Z).Additive := sorry

/-- Global sections with support in a closed subset, valued in modules over the global
section ring. -/
abbrev globalSectionsFunctor (Z : Closeds X) :=
  SheafOfModules.ClosedSubset.SectionsWithSupport.ambientFunctor X.ringCatSheaf Z ⋙
    RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace

/-- The right-derived global sections with support in a closed subset. -/
abbrev cohomology (Z : Closeds X) (F : X.Modules) (q : ℕ) : ModuleCat Γ(X, ⊤) :=
  ((globalSectionsFunctor Z).rightDerived q).obj F

/-- The ambient local-cohomology module sheaf supported on a closed subset. -/
abbrev cohomologySheaf (Z : Closeds X) (F : X.Modules) (q : ℕ) : X.Modules :=
  ((SheafOfModules.ClosedSubset.SectionsWithSupport.ambientFunctor X.ringCatSheaf Z).rightDerived
    q).obj F

/-- Local cohomology of a quasi-coherent module is quasi-coherent when the open
complement of the support is retrocompact. -/
instance cohomologySheaf_isQuasicoherent (Z : Closeds X) (F : X.Modules)
    [F.IsQuasicoherent] (q : ℕ) [Fact (IsRetrocompact (Z.compl : Set X))] :
    (cohomologySheaf Z F q).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Modules.Support
