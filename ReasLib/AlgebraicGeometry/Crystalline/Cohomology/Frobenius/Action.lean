/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.Frobenius
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.AffineBase
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.Frobenius.Crystal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Crystal
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

-- The explicit public sections map uses a private scalar comparison, as in the
-- existing crystalline derived-comparison owners.
set_option backward.privateInPublic true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients CrystallineRingedGeometry
open CrystallineModuleDerivedSections RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.Frobenius

/-- Pullback along `Spec(σ)` intertwines affine global functions with `σ`. -/
theorem sigmaBaseRingMap_comp {A : Type u} [CommRing A] (σ : A →+* A) :
    (CrystallineCoefficients.baseRingMap (Spec.map (CommRingCat.ofHom σ))).comp
        (CrystallineModuleDerivedSections.baseRingMap A) =
      (CrystallineModuleDerivedSections.baseRingMap A).comp σ := sorry

/-- Derived restriction along the lifted affine endomorphism agrees with
restriction along `σ` after the affine base identification. -/
private def sigmaRestrictionIso {A : Type u} [CommRing A] (σ : A →+* A) :
    ModuleCat.derivedRestrictionOfScalars.{u + 1, u + 1}
        (CrystallineCoefficients.baseRingMap (Spec.map (CommRingCat.ofHom σ))) ⋙
      baseRestriction A ≅
    baseRestriction A ⋙ ModuleCat.derivedRestrictionOfScalars.{u, u + 1} σ :=
  let b := CrystallineModuleDerivedSections.baseRingMap A
  let τ := CrystallineCoefficients.baseRingMap (Spec.map (CommRingCat.ofHom σ))
  (ExactFunctor.MapDerivedCategory.compFunctorIso
    (ExactFunctor.of (ModuleCat.restrictScalars.{u + 1} τ))
    (ExactFunctor.of (ModuleCat.restrictScalars.{u + 1} b))).symm ≪≫
    Functor.MapDerivedCategory.functorIso
      ((ModuleCat.restrictScalarsComp b τ).symm ≪≫
        ModuleCat.restrictScalarsComp' σ b (τ.comp b) (sigmaBaseRingMap_comp σ)) ≪≫
    ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (ModuleCat.restrictScalars.{u + 1} b))
      (ExactFunctor.of (ModuleCat.restrictScalars.{u + 1} σ))

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

/-- The Frobenius-lift projection induces a `σ`-semilinear map on ordinary
crystalline coefficients in derived global sections over `A`. -/
def sigmaSectionsPullback :
    derivedGlobalSections I γS hc x₀ s hp E ⟶
      (ModuleCat.derivedRestrictionOfScalars.{u, u + 1} σ).obj
        ((baseRestriction A).obj
          ((baseDerivedGlobalSections I γS hc
            (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))
            p s (twistPrimeNilpotent x₀ hp)).obj
              (twistedCrystal I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E))) :=
  (baseRestriction A).map
    ((sigmaMorphism I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD).baseSectionsPullbackToOrdinary
      (baseToGlobalSections I γS hc x₀ p s hp)
      (baseToGlobalSections I γS hc
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) p s (twistPrimeNilpotent x₀ hp))
      (CrystallineCoefficients.baseRingMap (Spec.map (CommRingCat.ofHom σ)))
      (baseActions_compatible I γS hc
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) I γS hc s s x₀
        (pullback.fst x₀ (Scheme.absoluteFrobenius p I.subscheme)) (specSigmaHom I s σ h_ideal h_over)
        (twist_over_specSigma I s σ h_ideal h_over h_p_mem h_sigma x₀)
        (twistPrimeNilpotent x₀ hp) hp hPD)
      (liftedOfCrystal I γS hc x₀ E p s hp)) ≫
    (sigmaRestrictionIso σ).hom.app _

/-- Affine crystalline base change along the Frobenius lift is the `A`-linear
adjoint of semilinear pullback on ordinary coefficients. -/
def sigmaBaseChange :
    (ModuleCat.derivedExtensionOfScalars.{u, u, u + 1} σ).obj
        (derivedGlobalSections I γS hc x₀ s hp E) ⟶
      (baseRestriction A).obj
        ((baseDerivedGlobalSections I γS hc
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))
          p s (twistPrimeNilpotent x₀ hp)).obj
            (twistedCrystal I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E)) :=
  (ModuleCat.derivedExtensionRestrictionHomEquiv.{u, u + 1} σ _ _).symm
    (sigmaSectionsPullback I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E)

/-- Under scalar adjunction, crystalline base change corresponds to semilinear
pullback of derived sections. -/
theorem sigmaBaseChange_spec :
    ModuleCat.derivedExtensionRestrictionHomEquiv.{u, u + 1} σ _ _
      (sigmaBaseChange I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E) =
    sigmaSectionsPullback I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E := sorry

/-- An ordinary coefficient Frobenius equips the lifted crystal with the
Frobenius-crystal structure for absolute crystalline pullback. -/
def coefficientCrystal
    (F_E : absoluteModule I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E ⟶
      liftedOfCrystal I γS hc x₀ E p s hp) :
    FrobeniusCrystal
      (absoluteMorphism I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD).modulePullback where
  obj := liftedOfCrystal I γS hc x₀ E p s hp
  frobenius := F_E

/-- Derived global sections send the ordinary coefficient Frobenius to its
map on crystalline cohomology over the lifted base ring. -/
def coefficientSectionsMap
    (F_E : absoluteModule I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E ⟶
      liftedOfCrystal I γS hc x₀ E p s hp) :
    (baseDerivedGlobalSections I γS hc x₀ p s hp).obj
        (absoluteCrystal I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E) ⟶
      (baseDerivedGlobalSections I γS hc x₀ p s hp).obj
        (derivedOfCrystal I γS hc x₀ p s hp E) :=
  (baseDerivedGlobalSections I γS hc x₀ p s hp).map
    ((RingedSite.Hom.moduleLocalization.{u + 1} (liftedRingedSite I γS hc x₀ p s hp)).map
      ((HomotopyCategory.singleFunctor _ (0 : ℤ)).map F_E))

variable [HasModulePullbackDerived (relativeMorphism I γS hc x₀ s hp)]
variable [HasModulePushforwardDerived (relativeMorphism I γS hc x₀ s hp)]
variable [HasModuleDerivedAdjunction (relativeMorphism I γS hc x₀ s hp)]

/-- Crystalline cohomology Frobenius is base change along `σ`, followed by
relative Frobenius pullback and the ordinary coefficient Frobenius. -/
def cohomologyMap
    (F_E : absoluteModule I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E ⟶
      liftedOfCrystal I γS hc x₀ E p s hp) :
    (ModuleCat.derivedExtensionOfScalars.{u, u, u + 1} σ).obj
        (derivedGlobalSections I γS hc x₀ s hp E) ⟶
      derivedGlobalSections I γS hc x₀ s hp E :=
  sigmaBaseChange I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E ≫
    (baseRestriction A).map
      (relativeSectionsPullback I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E) ≫
    (baseRestriction A).map
      (coefficientSectionsMap I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E F_E)

/-- The cohomological Frobenius factors through twisted coefficients and
ordinary absolute-Frobenius pullback coefficients. -/
theorem cohomologyMap_comp
    (F_E : absoluteModule I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E ⟶
      liftedOfCrystal I γS hc x₀ E p s hp) :
    cohomologyMap I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E F_E =
      sigmaBaseChange I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E ≫
        (baseRestriction A).map
          (relativeSectionsPullback I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E) ≫
        (baseRestriction A).map
          (coefficientSectionsMap I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E F_E) := sorry

variable [HasWeakSheafify
  (smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp) AddCommGrpCat.{u}]
variable [(smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp).WEqualsLocallyBijective
  AddCommGrpCat.{u}]
variable [∀ U : smallCrystallineSite (Spec (.of A)) I γS hc X x₀,
  HasWeakSheafify ((smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp).over U)
    AddCommGrpCat.{u}]
variable [∀ U : smallCrystallineSite (Spec (.of A)) I γS hc X x₀,
  ((smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp).over U).WEqualsLocallyBijective
    AddCommGrpCat.{u}]

/-- For a nondegenerate finite locally free Frobenius crystal on a proper
smooth scheme over a prime-local affine divided-power base, cohomological
Frobenius becomes invertible after inverting the prime when the base ring is
Noetherian and complete for its prime-adic topology. -/
theorem cohomologyMap_isIso_after_inverting_p
    (F_E : absoluteModule I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E ⟶
      liftedOfCrystal I γS hc x₀ E p s hp)
    [IsAdicComplete (Ideal.span {(p : A)}) A] [IsNoetherianRing A]
    [IsProper x₀] [Smooth x₀]
    [SheafOfModules.IsCrystalInFiniteLocallyFreeModules (ofCrystal I γS hc x₀ E p s hp)]
    (h_nondegenerate : FrobeniusCrystal.IsNondegenerate p
      (coefficientCrystal I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E F_E)) :
    IsIso ((ModuleCat.derivedExtensionOfScalars.{u, u, u + 1}
      (algebraMap A (Localization.Away (p : A)))).map
        (cohomologyMap I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E F_E)) := sorry

end AlgebraicGeometry.Scheme.Crystalline.Frobenius
