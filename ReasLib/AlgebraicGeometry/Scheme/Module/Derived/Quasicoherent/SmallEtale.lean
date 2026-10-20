/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose

/-!
# Derived quasi-coherent modules on the small étale site of a scheme

`DerivedQCoh.SmallEtale X` is the full subcategory of `D(𝒪_étale)` whose objects have
quasi-coherent cohomology sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Abelian-group-valued sheaf composition exists on the small étale topology of a scheme. -/
instance smallEtale_hasSheafCompose (X : Scheme.{u}) :
    X.smallEtaleTopology.HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) := sorry

/-- Modules on the small étale ringed site have normal monomorphisms and epimorphisms,
finite products, kernels, and cokernels. -/
theorem etaleModulesAbelian_axioms (X : Scheme.{u}) :
    IsNormalMonoCategory (SheafOfModules.{u} (Etale.Small.structureSheaf X)) ∧
      IsNormalEpiCategory (SheafOfModules.{u} (Etale.Small.structureSheaf X)) ∧
      CategoryTheory.Limits.HasFiniteProducts (SheafOfModules.{u} (Etale.Small.structureSheaf X)) ∧
      CategoryTheory.Limits.HasKernels (SheafOfModules.{u} (Etale.Small.structureSheaf X)) ∧
      CategoryTheory.Limits.HasCokernels (SheafOfModules.{u} (Etale.Small.structureSheaf X)) := sorry

/-- The category of modules on the small étale ringed site of a scheme is abelian. -/
instance etaleModulesAbelian (X : Scheme.{u}) :
    Abelian (SheafOfModules.{u} (Etale.Small.structureSheaf X)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := (etaleModulesAbelian_axioms X).1
  toIsNormalEpiCategory := (etaleModulesAbelian_axioms X).2.1
  has_finite_products := (etaleModulesAbelian_axioms X).2.2.1
  has_kernels := (etaleModulesAbelian_axioms X).2.2.2.1
  has_cokernels := (etaleModulesAbelian_axioms X).2.2.2.2

/-- The standard derived-category structure on modules on the small étale ringed site. -/
instance instHasDerivedCategory_etaleModules (X : Scheme.{u}) :
    HasDerivedCategory (SheafOfModules.{u} (Etale.Small.structureSheaf X)) :=
  HasDerivedCategory.standard _

namespace DerivedQCoh

/-- The property that every cohomology sheaf of a derived module on the small étale
ringed site is quasi-coherent. -/
abbrev smallEtaleProperty (X : Scheme.{u}) :
    ObjectProperty
      (DerivedCategory (SheafOfModules.{u} (Etale.Small.structureSheaf X))) :=
  DerivedCategory.cohomologyIn
    (SheafOfModules.isQuasicoherent (Etale.Small.structureSheaf X))

/-- The derived category of quasi-coherent modules on the small étale ringed site of `X`. -/
abbrev SmallEtale (X : Scheme.{u}) :=
  DerivedCategory.CohomologyIn
    (SheafOfModules.isQuasicoherent (Etale.Small.structureSheaf X))

namespace SmallEtale

/-- The inclusion of derived modules with quasi-coherent cohomology into `D(𝒪_étale)`. -/
abbrev inclusion (X : Scheme.{u}) :
    SmallEtale X ⥤
      DerivedCategory (SheafOfModules.{u} (Etale.Small.structureSheaf X)) :=
  (smallEtaleProperty X).ι

end SmallEtale

end DerivedQCoh

end AlgebraicGeometry.Scheme
