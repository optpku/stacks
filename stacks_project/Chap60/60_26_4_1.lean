/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.Frobenius.Action

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients CrystallineRingedGeometry
open CrystallineModuleDerivedSections RingedSite.ToposHom

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.Frobenius

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
variable [I.toModule.IsQuasicoherent] [Scheme.IsCharP I.subscheme p]
variable (h_p_mem : ∀ V : (Spec (.of A)).affineOpens, (p : Γ(Spec (.of A), V)) ∈ I.ideal V)
variable (h_sigma : ∀ x : A, σ x - x ^ p ∈ Ideal.span ({(p : A)} : Set A))
variable (hPD : ∀ (V W : (Spec (.of A)).affineOpens)
  (hVW : W.1 ≤ (Spec.map (CommRingCat.ofHom σ)) ⁻¹ᵁ V.1),
  (γS V).IsDPMorphism (γS W)
    ((Spec.map (CommRingCat.ofHom σ)).appLE V W hVW).hom)



variable [HasSheafify
  (crystallineZariskiTopology (Spec (.of A)) I γS hc X x₀) (Type (u + 1))]
variable [HasSheafify
  (crystallineZariskiTopology (Spec (.of A)) I γS hc
    (relativeFrobeniusTarget (p := p) x₀) (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))) (Type (u + 1))]
variable [HasSheafify
  (smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp) (Type (u + 1))]
variable [HasSheafify
  (smallCrystallineTopology p (Spec (.of A)) I γS hc s
    (relativeFrobeniusTarget (p := p) x₀) (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))
    (twistPrimeNilpotent x₀ hp)) (Type (u + 1))]
variable [(crystallineZariskiTopology (Spec (.of A)) I γS hc X x₀).HasSheafCompose
  (CategoryTheory.forget RingCat.{u + 1})]
variable [(crystallineZariskiTopology (Spec (.of A)) I γS hc
    (relativeFrobeniusTarget (p := p) x₀) (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))).HasSheafCompose
  (CategoryTheory.forget RingCat.{u + 1})]
variable [(smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp).HasSheafCompose
  (CategoryTheory.forget RingCat.{u + 1})]
variable [(smallCrystallineTopology p (Spec (.of A)) I γS hc s
    (relativeFrobeniusTarget (p := p) x₀) (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))
    (twistPrimeNilpotent x₀ hp)).HasSheafCompose
  (CategoryTheory.forget RingCat.{u + 1})]
variable [∀ P : (RelativeCRIS (Spec (.of A)) I γS hc
    (relativeFrobeniusTarget (p := p) x₀) (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))ᵒᵖ ⥤ Type (u + 1),
  (@CrystallineFunctor.of p inferInstance _ _ I I γS γS hc hc s s _ _
      (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) x₀ (pullback.fst x₀ (Scheme.absoluteFrobenius p I.subscheme)) (specSigmaHom I s σ h_ideal h_over)
      (twist_over_specSigma I s σ h_ideal h_over h_p_mem h_sigma x₀)
      (twistPrimeNilpotent x₀ hp) hp
      hPD).toRelativeFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (RelativeCRIS (Spec (.of A)) I γS hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (@CrystallineFunctor.of p inferInstance _ _ I I γS γS hc hc s s _ _
      x₀ (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) (relativeFrobenius (p := p) x₀) (idDividedPowerSchemeHom I s)
      ((relativeFrobenius_snd (p := p) x₀).trans (Category.comp_id x₀).symm) hp
      (twistPrimeNilpotent x₀ hp)
      (id_dividedPowers_compatible I γS)).toRelativeFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite (Spec (.of A)) I γS hc
    (relativeFrobeniusTarget (p := p) x₀) (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion (Spec (.of A)) I γS hc
      (relativeFrobeniusTarget (p := p) x₀) (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite (Spec (.of A)) I γS hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion (Spec (.of A)) I γS hc X x₀).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite (Spec (.of A)) I γS hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion (Spec (.of A)) I γS hc X x₀).op.HasLeftKanExtension P]
variable [∀ P : (smallCrystallineSite (Spec (.of A)) I γS hc
    (relativeFrobeniusTarget (p := p) x₀) (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)))ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion (Spec (.of A)) I γS hc
      (relativeFrobeniusTarget (p := p) x₀) (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))).op.HasLeftKanExtension P]
variable [IsGrothendieckAbelian
  (RingedSite.ModuleCat.{u + 1} (liftedRingedSite I γS hc x₀ p s hp))]
variable [IsGrothendieckAbelian
  (RingedSite.ModuleCat.{u + 1}
    (liftedRingedSite I γS hc (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) p s
      (twistPrimeNilpotent x₀ hp)))]

variable [(SheafOfModules.restrictScalars
  (sigmaMorphism I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
  (relativeMorphism I γS hc x₀ s hp).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
  (absoluteMorphism I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD).structureMap).IsRightAdjoint]

variable [(SheafOfModules.restrictScalars
  (RingedSite.ToposHom.id (liftedRingedSite I γS hc x₀ p s hp)).structureMap).IsRightAdjoint]

variable (E : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
variable [SectionsCoherent I γS hc x₀ E] [CrisModuleSheaf.IsCrystal E]

variable [HasModulePullbackDerived
  (sigmaMorphism I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD)]
variable [HasModulePushforwardDerived
  (sigmaMorphism I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD)]
variable [HasModuleDerivedAdjunction
  (sigmaMorphism I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD)]

/- 60.26.4.1: crystalline cohomology base change along the Frobenius lift. -/
@[stacks 07QC] #check
  (AlgebraicGeometry.Scheme.Crystalline.Frobenius.sigmaBaseChange
    I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E :
    (ModuleCat.derivedExtensionOfScalars.{u, u, u + 1} σ).obj
        (derivedGlobalSections I γS hc x₀ s hp E) ⟶
      (baseRestriction A).obj
        ((baseDerivedGlobalSections I γS hc
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))
          p s (twistPrimeNilpotent x₀ hp)).obj
            (twistedCrystal I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E)))

end AlgebraicGeometry.Scheme.Crystalline.Frobenius
