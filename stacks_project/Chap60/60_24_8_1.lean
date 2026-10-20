/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.BaseChangeMap
public import stacks_project.Chap60.Remark_60_24_9_Base_change_isomorphism_RingedGeometry

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf
open CrystallineRingedGeometry CrystallineCoefficients

universe u

section

variable {S X : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : S.affineOpens) (a : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen a))
    (S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom)
variable (x₀ : X ⟶ I.subscheme)
variable {p : ℕ} [Fact p.Prime]
variable {S' X' : Scheme.{u}} (I' : S'.IdealSheafData)
variable (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
variable (hc' : ∀ (V : S'.affineOpens) (a : Γ(S', V)),
  (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen a))
    (S'.presheaf.map (homOfLE (S'.basicOpen_le a)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (x'₀ : X' ⟶ I'.subscheme) (f : X ⟶ X')
variable (g : DividedPowerSchemeHom I I' s s')
variable (hf : f ≫ x'₀ = x₀ ≫ g.zeroFiberMap)
variable (hpX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (hpX' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))
variable (hγ : ∀ (V : S'.affineOpens) (W : S.affineOpens)
  (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
  (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom)

variable [HasSheafify (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1))]
variable [HasSheafify (crystallineZariskiTopology S' I' γ' hc' X' x'₀) (Type (u + 1))]
variable [HasSheafify (smallCrystallineTopology p S I γ hc s X x₀ hpX) (Type (u + 1))]
variable [HasSheafify (smallCrystallineTopology p S' I' γ' hc' s' X' x'₀ hpX')
  (Type (u + 1))]
variable [(crystallineZariskiTopology S I γ hc X x₀).HasSheafCompose
  (forget RingCat.{u + 1})]
variable [(crystallineZariskiTopology S' I' γ' hc' X' x'₀).HasSheafCompose
  (forget RingCat.{u + 1})]
variable [(smallCrystallineTopology p S I γ hc s X x₀ hpX).HasSheafCompose
  (forget RingCat.{u + 1})]
variable [(smallCrystallineTopology p S' I' γ' hc' s' X' x'₀ hpX').HasSheafCompose
  (forget RingCat.{u + 1})]
variable [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (CrystallineFunctor.of f g hf hpX hpX' hγ).toRelativeFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S I γ hc X x₀).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite S' I' γ' hc' X' x'₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S' I' γ' hc' X' x'₀).op.HasLeftKanExtension P]
variable [IsGrothendieckAbelian
  (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I γ hc x₀ p s hpX))]
variable [IsGrothendieckAbelian
  (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I' γ' hc' x'₀ p s' hpX'))]
variable [(SheafOfModules.restrictScalars
  (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ).structureMap).IsRightAdjoint]
variable [RingedSite.ToposHom.HasModulePullbackDerived
  (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)]
variable [RingedSite.ToposHom.HasModulePushforwardDerived
  (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction
  (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)]

/-- In the affine divided-power crystalline base-change setup, let `F'` be an
arbitrary module sheaf over `X'/S'`. The canonical map on crystalline cohomology is obtained by
derived scalar extension along the actual base-ring map induced by `g`, followed by the canonical
comparison
from the derived pullback to the ordinary pullback coefficient over `X/S`. -/
noncomputable def crystallineCohomologyBaseChange
    [IsAffine S] [IsAffine S']
    (F' : RingedSite.ModuleCat.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX')) :=
  let K := (RingedSite.Hom.moduleLocalization.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX')).obj
    ((HomotopyCategory.singleFunctor
      (RingedSite.ModuleCat.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX')) (0 : ℤ)).obj F')
  let f₀ := smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ
  let ordinaryPullback :=
    (Functor.totalLeftDerivedCounit
      (RingedSite.ToposHom.modulePullbackToDerived.{u + 1} f₀)
      (RingedSite.Hom.moduleLocalization.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX'))
      (RingedSite.Hom.ModuleQis.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX'))).app
      ((HomotopyCategory.singleFunctor
        (RingedSite.ModuleCat.{u + 1}
          (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX')) (0 : ℤ)).obj
        F')
  cohomologyBaseChange I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ K ≫
    (CategoryTheory.ModuleCat.derivedRestrictionOfScalars
      (CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX)).map
      ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)).map ordinaryPullback)

variable [IsAffine S] [IsAffine S']
variable (F' : RingedSite.ModuleCat.{u + 1}
  (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX'))

/- 60.24.8.1: the canonical crystalline cohomology base-change map for an arbitrary module
sheaf, with ordinary pullback coefficients, is the transpose along the actual base-ring map. -/
@[stacks 07MT] #check (CategoryTheory.ModuleCat.derivedExtensionRestrictionMap
  (CrystallineCoefficients.baseRingMap g.base)
  (let Ysite := CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX'
   let Xsite := CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX
   let coefficient := (HomotopyCategory.singleFunctor
     (RingedSite.ModuleCat.{u + 1} Ysite) (0 : ℤ)).obj F'
   let K := (RingedSite.Hom.moduleLocalization.{u + 1} Ysite).obj coefficient
   let f₀ := smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ
   let ordinaryPullback := (Functor.totalLeftDerivedCounit
     (RingedSite.ToposHom.modulePullbackToDerived.{u + 1} f₀)
     (RingedSite.Hom.moduleLocalization.{u + 1} Ysite)
     (RingedSite.Hom.ModuleQis.{u + 1} Ysite)).app coefficient
   let α := CrystallineCoefficients.baseToGlobalSections I' γ' hc' x'₀ p s' hpX'
   let β := CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX
   let σ := CrystallineCoefficients.baseRingMap g.base
   let cmp := crystallineDerivedGlobalSectionsIso
     I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ
   let ρ := crystallineBaseRestrictionIso
     I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ
   (CategoryTheory.ModuleCat.derivedRestrictionOfScalars α).map
        ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1} Ysite).map
            (f₀.moduleDerivedAdjunction.unit.app K) ≫
          cmp.inv.app (f₀.modulePullbackDerived.obj K)) ≫
      ρ.hom.app ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1} Xsite).obj
        (f₀.modulePullbackDerived.obj K)) ≫
      (CategoryTheory.ModuleCat.derivedRestrictionOfScalars σ).map
        ((CategoryTheory.ModuleCat.derivedRestrictionOfScalars β).map
          ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1} Xsite).map ordinaryPullback))) :
    (CategoryTheory.ModuleCat.derivedExtensionOfScalars.{u + 1, u + 1, u + 1}
      (CrystallineCoefficients.baseRingMap g.base)).obj
      ((CategoryTheory.ModuleCat.derivedRestrictionOfScalars
        (CrystallineCoefficients.baseToGlobalSections I' γ' hc' x'₀ p s' hpX')).obj
        ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1}
          (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX')).obj
          ((RingedSite.Hom.moduleLocalization.{u + 1}
            (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX')).obj
            ((HomotopyCategory.singleFunctor
              (RingedSite.ModuleCat.{u + 1}
                (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX'))
              (0 : ℤ)).obj F')))) ⟶
      (CategoryTheory.ModuleCat.derivedRestrictionOfScalars
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
