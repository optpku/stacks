/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- The category of modules on the small étale ringed site of a scheme is abelian. -/
instance etaleModulesAbelian (X : Scheme.{u}) :
    Abelian (RingedSite.ModuleCat.{u} (Etale.Small.ringedSite X)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- The standard derived-category structure on modules on the small étale ringed site. -/
instance instHasDerivedCategory_etaleModules (X : Scheme.{u}) :
    HasDerivedCategory (RingedSite.ModuleCat.{u} (Etale.Small.ringedSite X)) :=
  HasDerivedCategory.standard _

namespace DerivedQCoh

/-- The property that every cohomology sheaf of a derived module on the small étale
ringed site is quasi-coherent. -/
abbrev smallEtaleProperty (X : Scheme.{u}) :
    ObjectProperty
      (DerivedCategory (RingedSite.ModuleCat.{u} (Etale.Small.ringedSite X))) :=
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
      DerivedCategory (RingedSite.ModuleCat.{u} (Etale.Small.ringedSite X)) :=
  (smallEtaleProperty X).ι

/-- An object of `D(𝒪_étale)` lies in `SmallEtale X` iff every cohomology sheaf is
quasi-coherent. -/
theorem mem_iff (X : Scheme.{u})
    (E : DerivedCategory (RingedSite.ModuleCat.{u} (Etale.Small.ringedSite X))) :
    smallEtaleProperty X E ↔
      ∀ n : ℤ,
        SheafOfModules.isQuasicoherent (Etale.Small.structureSheaf X)
          ((DerivedCategory.homologyFunctor
              (RingedSite.ModuleCat.{u} (Etale.Small.ringedSite X)) n).obj E) :=
  sorry

end SmallEtale

end DerivedQCoh

end AlgebraicGeometry.Scheme
