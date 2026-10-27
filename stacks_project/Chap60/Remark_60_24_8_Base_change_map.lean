/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.StructureBaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline CrystallineRingedGeometry CrystallineCoefficients

universe u

section

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

variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I γ hc x₀ p s hpX))]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX'))]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (Scheme.AssociatedModule.smallCommRingedSite .zariski S))]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (Scheme.AssociatedModule.smallCommRingedSite .zariski S'))]
variable [RingedSite.ToposHom.HasModulePushforwardDerived (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)]
variable [RingedSite.ToposHom.HasModulePushforwardDerived ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom)]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction ((Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom)]

variable [IsAffine S] [IsAffine S']
variable (F' : RingedSite.ModuleCat.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX'))

/- Remark 60.24.8 (Base change map) (1): the canonical crystalline base-change map to the
small Zariski bases, with ordinary pullback coefficients. -/
@[stacks 07MS] #check (CrystallineRingedGeometry.crystallineStructureBaseChange
  I γ hc x₀ s hpX I' γ' hc' s' x'₀ f g hf hpX' hγ F' :
    let f₀ := smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ
    let τ := structureMorphismToSmall I γ hc x₀ s hpX
    let τ' := structureMorphismToSmall I' γ' hc' x'₀ s' hpX'
    let b := (Scheme.Crystalline.Ringed.zariskiHom g.base).toToposHom
    let coefficient := (HomotopyCategory.singleFunctor
      (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX')) (0 : ℤ)).obj F'
    let K := (RingedSite.Hom.moduleLocalization.{u + 1}
      (liftedRingedSite I' γ' hc' x'₀ p s' hpX')).obj coefficient
    b.modulePullbackDerived.obj (τ'.modulePushforwardDerived.obj K) ⟶
      τ.modulePushforwardDerived.obj
        ((RingedSite.ToposHom.modulePullbackToDerived.{u + 1} f₀).obj coefficient))

/- Remark 60.24.8 (Base change map) (2): on global sections this yields the crystalline
cohomology base-change map in the derived category of the affine base ring. -/
@[stacks 07MS] #check (CrystallineRingedGeometry.crystallineCohomologyBaseChange
  I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ F'  :
    (CategoryTheory.ModuleCat.derivedExtensionOfScalars.{u + 1, u + 1, u + 1}
      (CrystallineCoefficients.baseRingMap g.base)).obj
      ((CategoryTheory.ModuleCat.derivedRestrictionOfScalars.{u + 1, u + 1}
        (CrystallineCoefficients.baseToGlobalSections I' γ' hc' x'₀ p s' hpX')).obj
        ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1}
          (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX')).obj
          ((RingedSite.Hom.moduleLocalization.{u + 1}
            (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX')).obj
            ((HomotopyCategory.singleFunctor
              (RingedSite.ModuleCat.{u + 1}
                (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX'))
              (0 : ℤ)).obj F')))) ⟶
      (CategoryTheory.ModuleCat.derivedRestrictionOfScalars.{u + 1, u + 1}
        (CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX)).obj
        ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1}
          (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)).obj
          ((RingedSite.ToposHom.modulePullbackToDerived.{u + 1}
            (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)).obj
            ((HomotopyCategory.singleFunctor
              (RingedSite.ModuleCat.{u + 1}
                (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX'))
              (0 : ℤ)).obj F'))))

end

