module

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

/-- Restriction of global sections along a morphism of algebraic spaces. -/
abbrev globalSectionsRingMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsRing X ⟶ globalSectionsRing Y :=
  Atlas.globalSectionsRingMap f

/-- The overEtaleStructurePresheaf construction in the atlas presentation. -/
abbrev overEtaleStructurePresheaf (X : AlgebraicSpace S) :
    (Over X)ᵒᵖ ⥤ RingCat.{u} :=
  Atlas.overEtaleStructurePresheaf X

/-- The overEtaleStructureSheaf construction in the atlas presentation. -/
abbrev overEtaleStructureSheaf (X : AlgebraicSpace S) :
    Sheaf (overEtaleTopology X) RingCat.{u} :=
  Atlas.overEtaleStructureSheaf X

/-- The overEtaleRingedSite construction in the atlas presentation. -/
abbrev overEtaleRingedSite (X : AlgebraicSpace S) : RingedSite.{u + 1, u + 1, u} :=
  Atlas.overEtaleRingedSite X

/-- The smallToBigStructureSheafMap construction in the atlas presentation. -/
abbrev smallToBigStructureSheafMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheaf Y ⟶
      ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology Y) (overEtaleTopology X)).obj
        (overEtaleStructureSheaf X) :=
  Atlas.smallToBigStructureSheafMap f

/-- The etalePiRingedHom construction in the atlas presentation. -/
abbrev etalePiRingedHom (X : AlgebraicSpace S) :
    RingedSite.Hom (overEtaleRingedSite X) (ringedSite X) :=
  Atlas.etalePiRingedHom X

/-- The relocalizationRingedHom construction in the atlas presentation. -/
abbrev relocalizationRingedHom {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    RingedSite.Hom (overEtaleRingedSite X) (ringedSite Y) :=
  Atlas.relocalizationRingedHom f

/-- The relocalizationModuleFunctor construction in the atlas presentation. -/
abbrev relocalizationModuleFunctor {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    RingedSite.ModuleCat.{u + 1} (overEtaleRingedSite X) ⥤
      RingedSite.ModuleCat.{u + 1} (ringedSite Y) :=
  Atlas.relocalizationModuleFunctor f

/-- The relocalizationModuleDerived construction in the atlas presentation. -/
abbrev relocalizationModuleDerived {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}] :
    ModuleDerived.{u + 1} (overEtaleRingedSite X) ⥤
      ModuleDerived.{u + 1} (ringedSite Y) :=
  Atlas.relocalizationModuleDerived f

/-- The etaleSmallModulePullbackDerived construction in the atlas presentation. -/
abbrev etaleSmallModulePullbackDerived {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}]
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (etalePiRingedHom X))
      (ModuleQis.{u + 1} (ringedSite X))] :
    ModuleDerived.{u + 1} (ringedSite X) ⥤ ModuleDerived.{u + 1} (ringedSite Y) :=
  Atlas.etaleSmallModulePullbackDerived f

/- Lemma 84.5.4: the atlas ringed relocalization and its module functors. -/
#check (AlgebraicGeometry.AlgebraicSpace.Etale.Atlas.etalePiRingedHom_base :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (etalePiRingedHom X).base = relocalizationFunctor (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Atlas.relocalizationRingedHom_base :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X),
    (relocalizationRingedHom f).base = relocalizationFunctor f)

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Atlas.relocalizationModuleFunctor_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X),
    relocalizationModuleFunctor f =
      moduleInverseImage (relocalizationFunctor f) (overEtaleStructureSheaf X) ⋙
        SheafOfModules.restrictScalars.{u + 1} (smallToBigStructureSheafMap f))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Atlas.etaleSmallModulePullbackDerived_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}]
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (etalePiRingedHom X))
      (ModuleQis.{u + 1} (ringedSite X))],
    etaleSmallModulePullbackDerived f =
      modulePullbackDerived.{u + 1} (etalePiRingedHom X) ⋙
        relocalizationModuleDerived f)

end AlgebraicGeometry.AlgebraicSpace.Etale

end

end
