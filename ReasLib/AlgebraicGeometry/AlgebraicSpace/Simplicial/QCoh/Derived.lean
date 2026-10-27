/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CohomologyIn
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Homology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.QCoh.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Module.EtaleDerived

/-! # Unbounded derived categories with quasi-coherent homology -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}}

/-- Additive sheafification exists on the total étale site in the enlarged universe. -/
instance hasSheafify_etaleTotalRingedSite (U : SimplicialObject (AlgebraicSpace S)) :
    HasSheafify (etaleTotalRingedSite U).siteTopology AddCommGrpCat.{u + 1} := inferInstance

/-- Ext groups exist for enlarged-universe additive sheaves on the total étale site. -/
instance hasExt_etaleTotalRingedSite (U : SimplicialObject (AlgebraicSpace S)) :
    HasExt.{u + 1} (Sheaf (etaleTotalRingedSite U).siteTopology AddCommGrpCat.{u + 1}) := sorry

/-- Weak additive sheafification exists on the total étale site in the enlarged universe. -/
instance hasWeakSheafify_etaleTotalRingedSite (U : SimplicialObject (AlgebraicSpace S)) :
    HasWeakSheafify (etaleTotalRingedSite U).siteTopology AddCommGrpCat.{u + 1} := inferInstance

/-- Enlarged-universe additive sheafification equivalences are locally bijective. -/
instance wEqualsLocallyBijective_etaleTotalRingedSite (U : SimplicialObject (AlgebraicSpace S)) :
    (etaleTotalRingedSite U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := sorry

/-- The standard enlarged-universe derived category of total-site module sheaves exists. -/
@[reducible]
def etaleTotalRingedSite_hasDerivedCategory (U : SimplicialObject (AlgebraicSpace S)) :
    HasDerivedCategory (RingedSite.ModuleCat.{u + 1} (etaleTotalRingedSite U)) :=
  HasDerivedCategory.standard (RingedSite.ModuleCat.{u + 1} (etaleTotalRingedSite U))

/-- Additive sheafification exists on a spaces-étale site in the enlarged universe. -/
instance hasSheafify_spacesRingedSite (X : AlgebraicSpace S) :
    HasSheafify (spacesRingedSite X).siteTopology AddCommGrpCat.{u + 1} := inferInstance

/-- Ext groups exist for enlarged-universe additive sheaves on a spaces-étale site. -/
instance hasExt_spacesRingedSite (X : AlgebraicSpace S) :
    HasExt.{u + 1} (Sheaf (spacesRingedSite X).siteTopology AddCommGrpCat.{u + 1}) := sorry

/-- Weak additive sheafification exists on a spaces-étale site in the enlarged universe. -/
instance hasWeakSheafify_spacesRingedSite (X : AlgebraicSpace S) :
    HasWeakSheafify (spacesRingedSite X).siteTopology AddCommGrpCat.{u + 1} := inferInstance

/-- Enlarged-universe additive sheafification equivalences on a spaces-étale site
are locally bijective. -/
instance wEqualsLocallyBijective_spacesRingedSite (X : AlgebraicSpace S) :
    (spacesRingedSite X).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := sorry

/-- The standard enlarged-universe derived category of spaces-étale modules exists. -/
@[reducible]
def spacesRingedSite_hasDerivedCategory (X : AlgebraicSpace S) :
    HasDerivedCategory (RingedSite.ModuleCat.{u + 1} (spacesRingedSite X)) :=
  HasDerivedCategory.standard (RingedSite.ModuleCat.{u + 1} (spacesRingedSite X))

/-- Enlarged-universe quasi-coherent modules are the isomorphism closure of carrier lifts
of native quasi-coherent modules. -/
def spacesQuasiCoherentProperty (X : AlgebraicSpace S) :
    ObjectProperty (RingedSite.ModuleCat.{u + 1} (spacesRingedSite X)) :=
  fun M ↦ ∃ (N : RingedSite.ModuleCat.{u} (spacesRingedSite X)),
    spacesQuasiCoherentModuleProperty X N ∧
      Nonempty (M ≅ RingedSite.Module.carrierLift (spacesRingedSite X) N)

/-- Membership in the enlarged-universe quasi-coherent property is specified by a
native quasi-coherent module and an isomorphism to its carrier lift. -/
theorem mem_spacesQuasiCoherentProperty_iff (X : AlgebraicSpace S)
    {M : RingedSite.ModuleCat.{u + 1} (spacesRingedSite X)} :
    spacesQuasiCoherentProperty X M ↔
      ∃ (N : RingedSite.ModuleCat.{u} (spacesRingedSite X)),
        spacesQuasiCoherentModuleProperty X N ∧
          Nonempty (M ≅ RingedSite.Module.carrierLift (spacesRingedSite X) N) := sorry

/-- Carrier lifting preserves the enlarged-universe quasi-coherent property. -/
theorem carrierLift_mem_spacesQuasiCoherentProperty (X : AlgebraicSpace S)
    {N : RingedSite.ModuleCat.{u} (spacesRingedSite X)}
    (hN : spacesQuasiCoherentModuleProperty X N) :
    spacesQuasiCoherentProperty X (RingedSite.Module.carrierLift (spacesRingedSite X) N) := sorry

/-- The enlarged-universe unbounded derived category with quasi-coherent homology. -/
abbrev spacesDerivedQCoh (X : AlgebraicSpace S) :=
  RingedSite.Hom.ModuleCohomologyIn.{u + 1, u + 1, u + 1, u}
    (spacesRingedSite X) (spacesQuasiCoherentProperty X)

/-- Inclusion of enlarged-universe derived quasi-coherent objects into all derived modules. -/
abbrev spacesDerivedQCoh.inclusion (X : AlgebraicSpace S) :
    spacesDerivedQCoh X ⥤ RingedSite.Hom.ModuleDerived.{u + 1} (spacesRingedSite X) :=
  (RingedSite.Hom.moduleCohomologyIn.{u + 1, u + 1, u + 1, u}
    (spacesRingedSite X) (spacesQuasiCoherentProperty X)).ι

/-- Enlarged-universe derived membership is quasi-coherence in every integer degree. -/
theorem spacesDerivedQCoh.mem_iff (X : AlgebraicSpace S)
    (E : RingedSite.Hom.ModuleDerived.{u + 1} (spacesRingedSite X)) :
    RingedSite.Hom.moduleCohomologyIn.{u + 1, u + 1, u + 1, u}
        (spacesRingedSite X) (spacesQuasiCoherentProperty X) E ↔
      ∀ n : ℤ, spacesQuasiCoherentProperty X
        ((DerivedCategory.homologyFunctor
          (RingedSite.ModuleCat.{u + 1} (spacesRingedSite X)) n).obj E) := sorry

namespace QCohDerived

/-- All integer-degree native homology sheaves are quasi-coherent on the base space. -/
def baseProperty (X : AlgebraicSpace S) :
    ObjectProperty (RingedSite.NativeDerived.category.{u} (spacesRingedSite X)) :=
  fun E ↦ ∀ n : ℤ, spacesQuasiCoherentModuleProperty X
    ((RingedSite.NativeDerived.homologyFunctor.{u} (spacesRingedSite X) n).obj E)

/-- All integer-degree native homology sheaves are quasi-coherent on the total étale site. -/
def totalProperty (U : SimplicialObject (AlgebraicSpace S)) :
    ObjectProperty (RingedSite.NativeDerived.category.{u} (etaleTotalRingedSite U)) :=
  fun E ↦ ∀ n : ℤ, quasiCoherentModuleProperty U
    ((RingedSite.NativeDerived.homologyFunctor.{u} (etaleTotalRingedSite U) n).obj E)

/-- The unbounded native derived category with quasi-coherent homology on an algebraic space. -/
abbrev Base (X : AlgebraicSpace S) := (baseProperty X).FullSubcategory

/-- The unbounded native derived category with quasi-coherent homology on a simplicial space. -/
abbrev Total (U : SimplicialObject (AlgebraicSpace S)) := (totalProperty U).FullSubcategory

/-- Inclusion of the base quasi-coherent derived category into all native derived modules. -/
abbrev Base.inclusion (X : AlgebraicSpace S) :
    Base X ⥤ RingedSite.NativeDerived.category.{u} (spacesRingedSite X) :=
  (baseProperty X).ι

/-- Inclusion of the total quasi-coherent derived category into all native derived modules. -/
abbrev Total.inclusion (U : SimplicialObject (AlgebraicSpace S)) :
    Total U ⥤ RingedSite.NativeDerived.category.{u} (etaleTotalRingedSite U) :=
  (totalProperty U).ι

/-- Base membership means quasi-coherence of native homology in every integer degree. -/
theorem Base.mem_iff (X : AlgebraicSpace S)
    (E : RingedSite.NativeDerived.category.{u} (spacesRingedSite X)) :
    baseProperty X E ↔ ∀ n : ℤ, spacesQuasiCoherentModuleProperty X
      ((RingedSite.NativeDerived.homologyFunctor.{u} (spacesRingedSite X) n).obj E) := Iff.rfl

/-- Total membership means quasi-coherence of native homology in every integer degree. -/
theorem Total.mem_iff (U : SimplicialObject (AlgebraicSpace S))
    (E : RingedSite.NativeDerived.category.{u} (etaleTotalRingedSite U)) :
    totalProperty U E ↔ ∀ n : ℤ, quasiCoherentModuleProperty U
      ((RingedSite.NativeDerived.homologyFunctor.{u} (etaleTotalRingedSite U) n).obj E) := Iff.rfl

end QCohDerived

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
