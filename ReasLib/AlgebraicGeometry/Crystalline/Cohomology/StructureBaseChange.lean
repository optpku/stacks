/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.RingedMorphism.StructureComparison
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryBaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.BaseChange.Ordinary
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.CompositionIso
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.Comparison

@[expose] public section

set_option backward.privateInPublic true
set_option maxHeartbeats 2000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline CrystallineCoefficients

noncomputable section

universe u

namespace CrystallineRingedGeometry

variable {S X : Scheme.{u}} (I : S.IdealSheafData)
  (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
  (hc : ∀ (V : S.affineOpens) (a : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen a))
      (S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom)
  (x₀ : X ⟶ I.subscheme)


variable [HasSheafify (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1))]
variable [(crystallineZariskiTopology S I γ hc X x₀).HasSheafCompose (forget RingCat.{u + 1})]
variable [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (bigThickeningOverBase I γ hc x₀).op.HasPointwiseRightKanExtension P]


variable {p : ℕ} [Fact p.Prime]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (hpX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable [HasSheafify (smallCrystallineTopology p S I γ hc s X x₀ hpX) (Type (u + 1))]
variable [(smallCrystallineTopology p S I γ hc s X x₀ hpX).HasSheafCompose (forget RingCat.{u + 1})]
variable [∀ P : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S I γ hc X x₀).op.HasPointwiseRightKanExtension P]


variable {S' X' : Scheme.{u}} (I' : S'.IdealSheafData)
  (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
  (hc' : ∀ (V : S'.affineOpens) (a : Γ(S', V)),
    (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen a))
      (S'.presheaf.map (homOfLE (S'.basicOpen_le a)).op).hom)
  (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
  (x'₀ : X' ⟶ I'.subscheme) (f : X ⟶ X')
  (g : DividedPowerSchemeHom I I' s s') (hf : f ≫ x'₀ = x₀ ≫ g.zeroFiberMap)
  (hpX' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))
  (hγ : ∀ (V : S'.affineOpens) (W : S.affineOpens) (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom)
variable [HasSheafify (crystallineZariskiTopology S' I' γ' hc' X' x'₀) (Type (u + 1))]
variable [HasSheafify (smallCrystallineTopology p S' I' γ' hc' s' X' x'₀ hpX') (Type (u + 1))]
variable [(crystallineZariskiTopology S' I' γ' hc' X' x'₀).HasSheafCompose (forget RingCat.{u + 1})]
variable [(smallCrystallineTopology p S' I' γ' hc' s' X' x'₀ hpX').HasSheafCompose (forget RingCat.{u + 1})]
variable [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (CrystallineFunctor.of f g hf hpX hpX' hγ).toRelativeFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (RelativeCRIS S' I' γ' hc' X' x'₀)ᵒᵖ ⥤ Type (u + 1),
  (bigThickeningOverBase I' γ' hc' x'₀).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite S' I' γ' hc' X' x'₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S' I' γ' hc' X' x'₀).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite S' I' γ' hc' X' x'₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S' I' γ' hc' X' x'₀).op.HasLeftKanExtension P]

variable [(SheafOfModules.restrictScalars (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars (structureMorphismToSmall I γ hc x₀ s hpX).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars (structureMorphismToSmall I' γ' hc' x'₀ s' hpX').structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars (RingedSite.ToposHom.comp (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ) (structureMorphismToSmall I' γ' hc' x'₀ s' hpX')).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars (RingedSite.ToposHom.comp (structureMorphismToSmall I γ hc x₀ s hpX) ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom)).structureMap).IsRightAdjoint]
variable [RingedSite.ToposHom.HasModulePullbackDerived (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)]
variable [RingedSite.ToposHom.HasModulePullbackDerived (structureMorphismToSmall I γ hc x₀ s hpX)]
variable [RingedSite.ToposHom.HasModulePullbackDerived (structureMorphismToSmall I' γ' hc' x'₀ s' hpX')]
variable [RingedSite.ToposHom.HasModulePullbackDerived ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom)]
variable [RingedSite.ToposHom.HasModulePullbackDerived (RingedSite.ToposHom.comp (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ) (structureMorphismToSmall I' γ' hc' x'₀ s' hpX'))]
variable [RingedSite.ToposHom.HasModulePushforwardDerived (structureMorphismToSmall I γ hc x₀ s hpX)]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction (structureMorphismToSmall I γ hc x₀ s hpX)]
variable [RingedSite.ToposHom.HasModulePushforwardDerived (structureMorphismToSmall I' γ' hc' x'₀ s' hpX')]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction (structureMorphismToSmall I' γ' hc' x'₀ s' hpX')]

/-- Restriction of derived small-Zariski sections to the scheme's base ring of global functions. -/
private def structureSectionsRestriction (S : Scheme.{u}) :
    RingedSite.Hom.ModuleSections.Derived.{u + 1}
      (Scheme.AssociatedModule.smallCommRingedSite .zariski S) ⥤
        DerivedCategory (_root_.ModuleCat.{u + 1} (CrystallineCoefficients.baseRing S)) :=
  (_root_.ModuleCat.restrictScalars.{u + 1}
    (Scheme.Zariski.Small.globalFunctionsIso S).symm.toRingHom).mapDerivedCategory

/-- Derived sections of a structure direct image identify with crystalline derived sections with their actual base action. -/
private def structureSectionsIso
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1}
      (liftedRingedSite I γ hc x₀ p s hpX))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1}
      (Scheme.AssociatedModule.smallCommRingedSite .zariski S))]
    (h : (structureMorphismToSmall I γ hc x₀ s hpX).globalSectionsMap.hom.comp
      (Scheme.Zariski.Small.globalFunctionsIso S).symm.toRingHom =
        CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX)
    (K : RingedSite.Hom.ModuleDerived.{u + 1} (liftedRingedSite I γ hc x₀ p s hpX)) :
    (structureSectionsRestriction S).obj
      ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1}
        (Scheme.AssociatedModule.smallCommRingedSite .zariski S)).obj
          ((structureMorphismToSmall I γ hc x₀ s hpX).modulePushforwardDerived.obj K)) ≅
      (CategoryTheory.ModuleCat.derivedRestrictionOfScalars.{u + 1, u + 1}
        (CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX)).obj
          ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1}
            (liftedRingedSite I γ hc x₀ p s hpX)).obj K) :=
  let τ := structureMorphismToSmall I γ hc x₀ s hpX
  let α : CrystallineCoefficients.baseRing S →+* RingedSite.Hom.globalSectionsRing
      (Scheme.AssociatedModule.smallCommRingedSite .zariski S) :=
    (Scheme.Zariski.Small.globalFunctionsIso S).symm.toRingHom
  let Z := RingedSite.Hom.globalSectionsRing
    (Scheme.AssociatedModule.smallCommRingedSite .zariski S)
  let commZ : CommRing Z := @RingCat.commRingOfMulComm _
    (RingCat.limitOfComm_commutative
      (Scheme.AssociatedModule.StandardSmall.commStructureSheaf .zariski S).obj)
  let sections : RingedSite.Hom.ModuleSections.Derived.{u + 1}
      (liftedRingedSite I γ hc x₀ p s hpX) :=
    (RingedSite.Hom.moduleDerivedGlobalSections.{u + 1}
      (liftedRingedSite I γ hc x₀ p s hpX)).obj K
  (structureSectionsRestriction S).mapIso (τ.derivedGlobalSectionsPushforwardIso.app K).symm ≪≫
    (@CategoryTheory.ModuleCat.DerivedRestriction.compObjIso
      (CrystallineCoefficients.baseRing S) Z _ inferInstance commZ inferInstance
        α τ.globalSectionsMap.hom sections).symm ≪≫
    (eqToIso (congrArg
      (fun ρ : CrystallineCoefficients.baseRing S →+* RingedSite.Hom.globalSectionsRing
          (liftedRingedSite I γ hc x₀ p s hpX) =>
        (_root_.ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategory) h)).app sections

/-- The derived pullback square induced by the actual crystalline and small-Zariski geometric morphisms. -/
def structurePullbackSquare :
    ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom).modulePullbackDerived ⋙ (structureMorphismToSmall I γ hc x₀ s hpX).modulePullbackDerived ≅
      (structureMorphismToSmall I' γ' hc' x'₀ s' hpX').modulePullbackDerived ⋙ (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ).modulePullbackDerived :=
  let c := structureComparison I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ
  let e := RingedSite.ToposHom.modulePullbackIsoOfTwoIso c
  RingedSite.ToposHom.DerivedPullbackComposition.compComparisonIso
    (structureMorphismToSmall I γ hc x₀ s hpX) ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom) _ (e ≪≫ RingedSite.ToposHom.modulePullbackCompIso (structureMorphismToSmall I γ hc x₀ s hpX) ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom)) ≪≫
    (RingedSite.ToposHom.DerivedPullbackComposition.compComparisonIso
      (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ) (structureMorphismToSmall I' γ' hc' x'₀ s' hpX') _ (RingedSite.ToposHom.modulePullbackCompIso (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ) (structureMorphismToSmall I' γ' hc' x'₀ s' hpX'))).symm

/-- The crystalline structure-morphism base-change map for an arbitrary ordinary module and its ordinary crystalline pullback. -/
def crystallineStructureBaseChange
    (F' : RingedSite.ModuleCat.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX')) :=
  RingedSite.ToposHom.DerivedBaseChange.mapToOrdinary (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ) (structureMorphismToSmall I' γ' hc' x'₀ s' hpX') (structureMorphismToSmall I γ hc x₀ s hpX) ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom)
    (structurePullbackSquare I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ) F'

/-- The crystalline sheaf base-change map is the derived mate followed by direct image of the derived-to-ordinary counit. -/
theorem crystallineStructureBaseChange_spec
    (F' : RingedSite.ModuleCat.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX')) :
    crystallineStructureBaseChange I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ F' =
      let coefficient := (HomotopyCategory.singleFunctor
        (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX')) (0 : ℤ)).obj F'
      let K := (RingedSite.Hom.moduleLocalization.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX')).obj coefficient
      CategoryTheory.DerivedBaseChange.app (structureMorphismToSmall I' γ' hc' x'₀ s' hpX').moduleDerivedAdjunction (structureMorphismToSmall I γ hc x₀ s hpX).moduleDerivedAdjunction
        (structurePullbackSquare I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ) K ≫
        (structureMorphismToSmall I γ hc x₀ s hpX).modulePushforwardDerived.map
          ((Functor.totalLeftDerivedCounit (RingedSite.ToposHom.modulePullbackToDerived.{u + 1} (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ))
            (RingedSite.Hom.moduleLocalization.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX'))
            (RingedSite.Hom.ModuleQis.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX'))).app coefficient) := sorry

variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I γ hc x₀ p s hpX))]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX'))]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (Scheme.AssociatedModule.smallCommRingedSite .zariski S))]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (Scheme.AssociatedModule.smallCommRingedSite .zariski S'))]
variable [RingedSite.ToposHom.HasModulePushforwardDerived (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)]
variable [RingedSite.ToposHom.HasModulePushforwardDerived ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom)]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom)]

/-- The canonical scalar comparison for the small-Zariski morphism induced by the base map. -/
private def structureScalarComparison
    (h : ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom).globalSectionsMap.hom.comp
      (Scheme.Zariski.Small.globalFunctionsIso S').symm.toRingHom =
        ((Scheme.Zariski.Small.globalFunctionsIso S).symm.toRingHom).comp (baseRingMap g.base))
    (K : RingedSite.Hom.ModuleDerived.{u + 1}
      (Scheme.AssociatedModule.smallCommRingedSite .zariski S')) :
    (CategoryTheory.ModuleCat.derivedExtensionOfScalars.{u + 1, u + 1, u + 1}
      (baseRingMap g.base)).obj
        ((structureSectionsRestriction S').obj
          ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1}
            (Scheme.AssociatedModule.smallCommRingedSite .zariski S')).obj K)) ⟶
      (structureSectionsRestriction S).obj
        ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1}
          (Scheme.AssociatedModule.smallCommRingedSite .zariski S)).obj
            (((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom).modulePullbackDerived.obj K)) :=
  @RingedSite.ToposHom.baseScalarComparison _ _ _ _ _ _ _ _ _ _
    (RingCat.limitOfComm_commutative
      (Scheme.AssociatedModule.StandardSmall.commStructureSheaf .zariski S).obj)
    (RingCat.limitOfComm_commutative
      (Scheme.AssociatedModule.StandardSmall.commStructureSheaf .zariski S').obj)
    ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom) _ _ _ _ _ _ _
    (Scheme.Zariski.Small.globalFunctionsIso S').symm.toRingHom
    (Scheme.Zariski.Small.globalFunctionsIso S).symm.toRingHom
    (baseRingMap g.base) h K

/-- Taking derived sections of crystalline sheaf base change, after the canonical scalar comparison, gives crystalline cohomology base change. -/
theorem crystallineStructureBaseChange_globalSections [IsAffine S] [IsAffine S']
    (F' : RingedSite.ModuleCat.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX')) :
    let c := (HomotopyCategory.singleFunctor
      (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX')) (0 : ℤ)).obj F'
    let K := (RingedSite.Hom.moduleLocalization.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX')).obj c
    let L := (RingedSite.ToposHom.modulePullbackToDerived.{u + 1} (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)).obj c
    let α := (Scheme.Zariski.Small.globalFunctionsIso S).symm.toRingHom
    let α' := (Scheme.Zariski.Small.globalFunctionsIso S').symm.toRingHom
    let laws := structureBaseActions_laws I γ hc x₀ s hpX I' γ' hc' s' x'₀ g hpX'
    crystallineCohomologyBaseChange I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ F' =
      (CategoryTheory.ModuleCat.derivedExtensionOfScalars.{u + 1, u + 1, u + 1} (baseRingMap g.base)).map
        (structureSectionsIso I' γ' hc' x'₀ s' hpX' laws.2.1 K).inv ≫
      structureScalarComparison I s I' s' g laws.2.2
        ((structureMorphismToSmall I' γ' hc' x'₀ s' hpX').modulePushforwardDerived.obj K) ≫
      (structureSectionsRestriction S).map
        ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1}
          (Scheme.AssociatedModule.smallCommRingedSite .zariski S)).map
            (crystallineStructureBaseChange I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ F')) ≫
      (structureSectionsIso I γ hc x₀ s hpX laws.1 L).hom := sorry

end CrystallineRingedGeometry
