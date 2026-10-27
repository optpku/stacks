/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ModuleComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AtlasModuleComparison

/-! # Atlas ringed-site compatibility -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open RingedSite.Hom RingedSite.Cocontinuous

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

variable {S : Scheme.{u}}

/-!
These six names are chapter-level aliases for the Atlas owner.  They do not
collide with the Big-site owners and preserve the public interface used by
older Chapter 84 facades.
-/

abbrev globalSectionsRingMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsRing X ⟶ globalSectionsRing Y :=
  Atlas.globalSectionsRingMap f

abbrev overEtaleStructurePresheaf (X : AlgebraicSpace S) :
    (Over X)ᵒᵖ ⥤ RingCat.{u} :=
  Atlas.overEtaleStructurePresheaf X

abbrev overEtaleStructureSheaf (X : AlgebraicSpace S) :
    Sheaf (overEtaleTopology X) RingCat.{u} :=
  Atlas.overEtaleStructureSheaf X

abbrev overEtaleRingedSite (X : AlgebraicSpace S) : RingedSite.{u + 1, u + 1, u} :=
  Atlas.overEtaleRingedSite X

abbrev etalePiRingedHom (X : AlgebraicSpace S) :
    RingedSite.Hom (overEtaleRingedSite X) (ringedSite X) :=
  Atlas.etalePiRingedHom X

abbrev relocalizationRingedHom {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    RingedSite.Hom (overEtaleRingedSite X) (ringedSite Y) :=
  Atlas.relocalizationRingedHom f

end AlgebraicGeometry.AlgebraicSpace.Etale

/-!
The four colliding module constructions are genuinely the Atlas-site objects,
whose domain uses `Atlas.overEtaleRingedSite`.  They are therefore exposed
under a chapter-local namespace instead of being given the Big-site owner
names in `AlgebraicGeometry.AlgebraicSpace.Etale`.
-/

namespace StacksProject.Chap84.Lemma_84_5_4_Ringed

open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open RingedSite.Hom RingedSite.Cocontinuous

variable {S : Scheme.{u}}

abbrev smallToBigStructureSheafMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheaf Y ⟶
      ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology Y) (overEtaleTopology X)).obj
        (AlgebraicGeometry.AlgebraicSpace.Etale.Atlas.overEtaleStructureSheaf X) :=
  AlgebraicGeometry.AlgebraicSpace.Etale.Atlas.smallToBigStructureSheafMap f

abbrev relocalizationModuleFunctor {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    RingedSite.ModuleCat.{u + 1}
        (AlgebraicGeometry.AlgebraicSpace.Etale.Atlas.overEtaleRingedSite X) ⥤
      RingedSite.ModuleCat.{u + 1} (ringedSite Y) :=
  AlgebraicGeometry.AlgebraicSpace.Etale.Atlas.relocalizationModuleFunctor f

abbrev relocalizationModuleDerived {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}] :
    ModuleDerived.{u + 1}
        (AlgebraicGeometry.AlgebraicSpace.Etale.Atlas.overEtaleRingedSite X) ⥤
      ModuleDerived.{u + 1} (ringedSite Y) :=
  AlgebraicGeometry.AlgebraicSpace.Etale.Atlas.relocalizationModuleDerived f

abbrev etaleSmallModulePullbackDerived {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}]
    [(AlgebraicGeometry.AlgebraicSpace.Etale.Atlas.etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1}
        (AlgebraicGeometry.AlgebraicSpace.Etale.Atlas.etalePiRingedHom X))
      (ModuleQis.{u + 1} (ringedSite X))] :
    ModuleDerived.{u + 1} (ringedSite X) ⥤ ModuleDerived.{u + 1} (ringedSite Y) :=
  AlgebraicGeometry.AlgebraicSpace.Etale.Atlas.etaleSmallModulePullbackDerived f

end StacksProject.Chap84.Lemma_84_5_4_Ringed

end

end
