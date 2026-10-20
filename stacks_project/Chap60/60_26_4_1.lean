module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.BaseChangeMap
import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
import stacks_project.Chap60.Theorem_60_26_4

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients CrystallineRingedGeometry
open SheafOfModules CrystallineModuleDerivedSections
open RingedSite.Hom RingedSite.ToposHom
open Scheme.IdealSheafData CategoryTheory.ModuleCat.DerivedExtension

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
variable (s : Spec (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (hp : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (σ : A →+* A)
variable (h_ideal : I.comap (Spec.map (CommRingCat.ofHom σ)) ≤ I)
variable (h_over : Spec.map (CommRingCat.ofHom σ) ≫ s = s)
variable (h_sigma : ∀ x : A, σ x - x ^ p ∈ Ideal.span ({(p : A)} : Set A))
variable (hPD : ∀ (V W : (Spec (.of A)).affineOpens)
  (hVW : W.1 ≤ (Spec.map (CommRingCat.ofHom σ)) ⁻¹ᵁ V.1),
  (γS V).IsDPMorphism (γS W)
    ((Spec.map (CommRingCat.ofHom σ)).appLE V W hVW).hom)
variable [Scheme.IsCharP I.subscheme p]
variable [HasSheafify
  (crystallineZariskiTopology (Spec (.of A)) I γS hc X x₀) (Type (u + 1))]
variable [HasSheafify
  (crystallineZariskiTopology (Spec (.of A)) I γS hc
    (frobeniusTwist p x₀) (frobeniusTwistOver p x₀)) (Type (u + 1))]
variable [HasSheafify
  (smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp) (Type (u + 1))]
variable [HasSheafify
  (smallCrystallineTopology p (Spec (.of A)) I γS hc s
    (frobeniusTwist p x₀) (frobeniusTwistOver p x₀)
    (relativeFrobeniusTarget_p_nilpotent I x₀ hp)) (Type (u + 1))]
variable [(crystallineZariskiTopology (Spec (.of A)) I γS hc X x₀).HasSheafCompose
  (CategoryTheory.forget RingCat.{u + 1})]
variable [(crystallineZariskiTopology (Spec (.of A)) I γS hc
    (frobeniusTwist p x₀) (frobeniusTwistOver p x₀)).HasSheafCompose
  (CategoryTheory.forget RingCat.{u + 1})]
variable [(smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp).HasSheafCompose
  (CategoryTheory.forget RingCat.{u + 1})]
variable [(smallCrystallineTopology p (Spec (.of A)) I γS hc s
    (frobeniusTwist p x₀) (frobeniusTwistOver p x₀)
    (relativeFrobeniusTarget_p_nilpotent I x₀ hp)).HasSheafCompose
  (CategoryTheory.forget RingCat.{u + 1})]
variable [∀ P : (RelativeCRIS (Spec (.of A)) I γS hc
    (frobeniusTwist p x₀) (frobeniusTwistOver p x₀))ᵒᵖ ⥤ Type (u + 1),
  (@CrystallineFunctor.of p inferInstance _ _ I I γS γS hc hc s s _ _
      (frobeniusTwistOver p x₀) x₀ (frobeniusTwistToSource p x₀)
      (specSigmaHom I s σ h_ideal h_over)
      (frobeniusTwist_over_specSigma I x₀ s σ h_ideal h_over h_sigma)
      (relativeFrobeniusTarget_p_nilpotent I x₀ hp) hp
      (specSigmaHom_dividedPowers_compatible I γS s σ h_ideal h_over hPD)).toRelativeFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (RelativeCRIS (Spec (.of A)) I γS hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (@CrystallineFunctor.of p inferInstance _ _ I I γS γS hc hc s s _ _
      x₀ (frobeniusTwistOver p x₀) (frobeniusRelative p x₀)
      (idDividedPowerSchemeHom I s) (relativeFrobenius_over_id I x₀ s) hp
      (relativeFrobeniusTarget_p_nilpotent I x₀ hp)
      (idDividedPowerSchemeHom_dividedPowers_compatible_spec I γS hc s)).toRelativeFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite (Spec (.of A)) I γS hc
    (frobeniusTwist p x₀) (frobeniusTwistOver p x₀))ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion (Spec (.of A)) I γS hc
      (frobeniusTwist p x₀) (frobeniusTwistOver p x₀)).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite (Spec (.of A)) I γS hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion (Spec (.of A)) I γS hc X x₀).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite (Spec (.of A)) I γS hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion (Spec (.of A)) I γS hc X x₀).op.HasLeftKanExtension P]
variable [∀ P : (smallCrystallineSite (Spec (.of A)) I γS hc
    (frobeniusTwist p x₀) (frobeniusTwistOver p x₀))ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion (Spec (.of A)) I γS hc
      (frobeniusTwist p x₀) (frobeniusTwistOver p x₀)).op.HasLeftKanExtension P]
variable [IsGrothendieckAbelian
  (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I γS hc x₀ p s hp))]
variable [IsGrothendieckAbelian
  (RingedSite.ModuleCat.{u + 1}
    (liftedRingedSite I γS hc (frobeniusTwistOver p x₀) p s
      (relativeFrobeniusTarget_p_nilpotent I x₀ hp)))]
variable [(SheafOfModules.restrictScalars
  (sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD).structureMap).IsRightAdjoint]
variable [HasModulePullbackDerived
  (sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD)]
variable [HasModulePushforwardDerived
  (sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD)]
variable [HasModuleDerivedAdjunction
  (sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD)]
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
variable [SectionsCoherent I γS hc x₀ F] [CrisModuleSheaf.IsCrystal F]

/- 60.26.4.1: crystalline cohomology base change along σ. -/
@[stacks 07QC] #check (CategoryTheory.ModuleCat.derivedExtensionRestrictionMap
  (CrystallineCoefficients.baseRingMap
    (specSigmaHom I s σ h_ideal h_over).base)
  (let Ysite := liftedRingedSite I γS hc x₀ p s hp
   let Xsite := liftedRingedSite I γS hc (frobeniusTwistOver p x₀) p s
      (relativeFrobeniusTarget_p_nilpotent I x₀ hp)
   let coefficient := (HomotopyCategory.singleFunctor
     (RingedSite.ModuleCat.{u + 1} Ysite) (0 : ℤ)).obj
       (liftedOfCrystal I γS hc x₀ F p s hp)
   let K := derivedOfCrystal I γS hc x₀ p s hp F
   let f₀ := sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD
   let ordinaryPullback :=
     (Functor.totalLeftDerivedCounit
       (RingedSite.ToposHom.modulePullbackToDerived.{u + 1} f₀)
       (RingedSite.Hom.moduleLocalization.{u + 1} Ysite)
       (RingedSite.Hom.ModuleQis.{u + 1} Ysite)).app coefficient
   let α := baseToGlobalSections I γS hc x₀ p s hp
   let β := baseToGlobalSections I γS hc (frobeniusTwistOver p x₀) p s
      (relativeFrobeniusTarget_p_nilpotent I x₀ hp)
   let σ' := CrystallineCoefficients.baseRingMap
      (specSigmaHom I s σ h_ideal h_over).base
   let cmp := crystallineDerivedGlobalSectionsIso I γS hc
      (frobeniusTwistOver p x₀) I γS hc s s x₀
      (frobeniusTwistToSource p x₀) (specSigmaHom I s σ h_ideal h_over)
      (frobeniusTwist_over_specSigma I x₀ s σ h_ideal h_over h_sigma)
      (relativeFrobeniusTarget_p_nilpotent I x₀ hp) hp
      (specSigmaHom_dividedPowers_compatible I γS s σ h_ideal h_over hPD)
   let ρ := crystallineBaseRestrictionIso I γS hc
      (frobeniusTwistOver p x₀) I γS hc s s x₀
      (frobeniusTwistToSource p x₀) (specSigmaHom I s σ h_ideal h_over)
      (frobeniusTwist_over_specSigma I x₀ s σ h_ideal h_over h_sigma)
      (relativeFrobeniusTarget_p_nilpotent I x₀ hp) hp
      (specSigmaHom_dividedPowers_compatible I γS s σ h_ideal h_over hPD)
   (CategoryTheory.ModuleCat.derivedRestrictionOfScalars α).map
      ((moduleDerivedGlobalSections.{u + 1} Ysite).map
        (f₀.moduleDerivedAdjunction.unit.app K) ≫
        cmp.inv.app (f₀.modulePullbackDerived.obj K)) ≫
      ρ.hom.app ((moduleDerivedGlobalSections.{u + 1} Xsite).obj
        (f₀.modulePullbackDerived.obj K)) ≫
      (CategoryTheory.ModuleCat.derivedRestrictionOfScalars σ').map
        ((CategoryTheory.ModuleCat.derivedRestrictionOfScalars β).map
          ((moduleDerivedGlobalSections.{u + 1} Xsite).map ordinaryPullback))) :
    (CategoryTheory.ModuleCat.derivedExtensionOfScalars.{u + 1, u + 1, u + 1}
      (CrystallineCoefficients.baseRingMap (specSigmaHom I s σ h_ideal h_over).base)).obj
      ((CategoryTheory.ModuleCat.derivedRestrictionOfScalars
        (baseToGlobalSections I γS hc x₀ p s hp)).obj
        ((moduleDerivedGlobalSections.{u + 1}
          (liftedRingedSite I γS hc x₀ p s hp)).obj
          ((RingedSite.Hom.moduleLocalization.{u + 1}
            (liftedRingedSite I γS hc x₀ p s hp)).obj
            ((HomotopyCategory.singleFunctor
              (RingedSite.ModuleCat.{u + 1}
                (liftedRingedSite I γS hc x₀ p s hp)) (0 : ℤ)).obj
              (liftedOfCrystal I γS hc x₀ F p s hp))))) ⟶
      ((CategoryTheory.ModuleCat.derivedRestrictionOfScalars
        (baseToGlobalSections I γS hc (frobeniusTwistOver p x₀) p s
          (relativeFrobeniusTarget_p_nilpotent I x₀ hp))).obj
        ((moduleDerivedGlobalSections.{u + 1}
          (liftedRingedSite I γS hc (frobeniusTwistOver p x₀) p s
            (relativeFrobeniusTarget_p_nilpotent I x₀ hp))).obj
          ((RingedSite.ToposHom.modulePullbackToDerived.{u + 1}
            (sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD)).obj
            ((HomotopyCategory.singleFunctor
              (RingedSite.ModuleCat.{u + 1}
                (liftedRingedSite I γS hc x₀ p s hp)) (0 : ℤ)).obj
              (liftedOfCrystal I γS hc x₀ F p s hp))))))

end AlgebraicGeometry.Scheme.Crystalline
