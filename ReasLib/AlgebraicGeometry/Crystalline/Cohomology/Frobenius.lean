/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Frobenius.Relative
public import ReasLib.AlgebraicGeometry.Crystalline.Functoriality.Abelian
public import ReasLib.AlgebraicGeometry.Crystalline.RingedMorphism.Relative
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.SectionsPullback
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Comparison

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients CrystallineRingedGeometry
open RingedSite.ToposHom

noncomputable section

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

/-- The small crystalline ringed morphism induced by `X^(1) ⟶ X` over `Spec(σ)`. -/
abbrev sigmaMorphism :
    RingedSite.ToposHom
      (liftedRingedSite I γS hc (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) p s
        (twistPrimeNilpotent x₀ hp))
      (liftedRingedSite I γS hc x₀ p s hp) :=
  smallRingedMorphism I γS hc (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) I γS hc s s x₀
    (pullback.fst x₀ (Scheme.absoluteFrobenius p I.subscheme)) (specSigmaHom I s σ h_ideal h_over)
    (twist_over_specSigma I s σ h_ideal h_over h_p_mem h_sigma x₀)
    (twistPrimeNilpotent x₀ hp) hp
    hPD

/-- The small crystalline ringed morphism induced by relative Frobenius over `id_S`. -/
abbrev relativeMorphism :
    RingedSite.ToposHom
      (liftedRingedSite I γS hc x₀ p s hp)
      (liftedRingedSite I γS hc (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) p s
        (twistPrimeNilpotent x₀ hp)) :=
  smallRingedMorphism I γS hc x₀ I γS hc s s (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))
    (relativeFrobenius (p := p) x₀) (idDividedPowerSchemeHom I s)
    ((relativeFrobenius_snd (p := p) x₀).trans (Category.comp_id x₀).symm) hp
    (twistPrimeNilpotent x₀ hp)
    (id_dividedPowers_compatible I γS)

/-- The composite of relative Frobenius with the Frobenius-lift projection,
as a morphism of crystalline ringed topoi. -/
abbrev absoluteMorphism :=
  (relativeMorphism I γS hc x₀ s hp).comp
    (sigmaMorphism I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD)

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

/-- The ordinary pullback of a crystal along the Frobenius-lift projection. -/
def twistedModule :=
  (sigmaMorphism I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD).modulePullback.obj
    (liftedOfCrystal I γS hc x₀ E p s hp)

/-- The ordinary crystalline absolute-Frobenius pullback of a crystal,
using the composite crystalline morphism. -/
def absoluteModule :=
  (absoluteMorphism I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD).modulePullback.obj
    (liftedOfCrystal I γS hc x₀ E p s hp)

/-- The Frobenius-twisted ordinary coefficient module placed in degree zero
and localized in the crystalline derived category. -/
def twistedCrystal :=
  (RingedSite.Hom.moduleLocalization.{u + 1}
    (liftedRingedSite I γS hc (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))
      p s (twistPrimeNilpotent x₀ hp))).obj
    ((HomotopyCategory.singleFunctor _ (0 : ℤ)).obj
      (twistedModule I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E))

/-- The ordinary absolute-Frobenius pullback coefficient placed in degree zero
and localized in the crystalline derived category. -/
def absoluteCrystal :=
  (RingedSite.Hom.moduleLocalization.{u + 1} (liftedRingedSite I γS hc x₀ p s hp)).obj
    ((HomotopyCategory.singleFunctor _ (0 : ℤ)).obj
      (absoluteModule I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E))

/-- Ordinary relative-Frobenius pullback of the twisted coefficient identifies
with ordinary pullback along the composite crystalline morphism. -/
def pullbackCoefficientIso :
    (relativeMorphism I γS hc x₀ s hp).modulePullback.obj
      (twistedModule I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E) ≅
    absoluteModule I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E :=
  ((CategoryTheory.SimplicialSites.modulePullbackCompIso
    (relativeMorphism I γS hc x₀ s hp)
    (sigmaMorphism I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD)).app
      (liftedOfCrystal I γS hc x₀ E p s hp)).symm

/-- Relative crystalline Frobenius respects the actual actions of the same
divided-power base ring on global functions. -/
theorem relative_baseActions :
    (relativeMorphism I γS hc x₀ s hp).globalSectionsMap.hom.comp
      (baseToGlobalSections I γS hc
        (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))
        p s (twistPrimeNilpotent x₀ hp)) =
    (baseToGlobalSections I γS hc x₀ p s hp).comp (RingHom.id (baseRing (Spec (.of A)))) := sorry

variable [HasModulePullbackDerived (relativeMorphism I γS hc x₀ s hp)]
variable [HasModulePushforwardDerived (relativeMorphism I γS hc x₀ s hp)]
variable [HasModuleDerivedAdjunction (relativeMorphism I γS hc x₀ s hp)]

/-- Relative Frobenius induces a same-base map from derived crystalline sections
of the ordinary twisted coefficient to those of the ordinary absolute-Frobenius
pullback coefficient. -/
def relativeSectionsPullback :
    (baseDerivedGlobalSections I γS hc
      (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme))
      p s (twistPrimeNilpotent x₀ hp)).obj
        (twistedCrystal I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E) ⟶
    (baseDerivedGlobalSections I γS hc x₀ p s hp).obj
      (absoluteCrystal I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E) :=
  (relativeMorphism I γS hc x₀ s hp).sameBaseSectionsPullback
    (baseToGlobalSections I γS hc
      (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) p s (twistPrimeNilpotent x₀ hp))
    (baseToGlobalSections I γS hc x₀ p s hp) (relative_baseActions I γS hc x₀ s hp)
    (twistedModule I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E) ≫
      (baseDerivedGlobalSections I γS hc x₀ p s hp).map
        ((RingedSite.Hom.moduleLocalization.{u + 1} (liftedRingedSite I γS hc x₀ p s hp)).map
          ((HomotopyCategory.singleFunctor _ (0 : ℤ)).map
            (pullbackCoefficientIso I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E).hom))

/-- The relative-Frobenius sections map is ordinary same-base pullback followed
by derived sections of the canonical degree-zero coefficient comparison. -/
theorem relativeSectionsPullback_eq :
    relativeSectionsPullback I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E =
      (relativeMorphism I γS hc x₀ s hp).sameBaseSectionsPullback
        (baseToGlobalSections I γS hc
          (pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme)) p s (twistPrimeNilpotent x₀ hp))
        (baseToGlobalSections I γS hc x₀ p s hp) (relative_baseActions I γS hc x₀ s hp)
        (twistedModule I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E) ≫
          (baseDerivedGlobalSections I γS hc x₀ p s hp).map
            ((RingedSite.Hom.moduleLocalization.{u + 1} (liftedRingedSite I γS hc x₀ p s hp)).map
              ((HomotopyCategory.singleFunctor _ (0 : ℤ)).map
                (pullbackCoefficientIso I γS hc x₀ s hp σ h_ideal h_over h_p_mem h_sigma hPD E).hom)) := sorry

end AlgebraicGeometry.Scheme.Crystalline.Frobenius
