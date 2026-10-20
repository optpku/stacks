module

public import stacks_project.Chap60.Remark_60_24_9_Base_change_isomorphism_RingedGeometry
public import stacks_project.Chap60.Lemma_60_25_4_Linearization
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Relative
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Crystalline
open Scheme.IdealSheafData
open CrystallineModuleSheaf CrystallineCoefficients CrystallineRingedGeometry
open RingedSite.ToposHom ComplexShape

universe u

@[expose] public section

noncomputable section

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

namespace FrobeniusSections

/-- The Frobenius twist `X^(1)` of `X ⟶ S₀`. -/
abbrev frobeniusTwist (p : ℕ) [Fact p.Prime] {X S₀ : Scheme.{u}}
    [Scheme.IsCharP S₀ p] (x₀ : X ⟶ S₀) : Scheme.{u} :=
  @relativeFrobeniusTarget p inferInstance X S₀ x₀ inferInstance

/-- The structure map `X^(1) ⟶ S₀`. -/
abbrev frobeniusTwistOver (p : ℕ) [Fact p.Prime] {X S₀ : Scheme.{u}}
    [Scheme.IsCharP S₀ p] (x₀ : X ⟶ S₀) : frobeniusTwist p x₀ ⟶ S₀ :=
  pullback.snd x₀ (Scheme.absoluteFrobenius p S₀)

/-- The comparison `X^(1) ⟶ X` in the defining pullback square. -/
abbrev frobeniusTwistToSource (p : ℕ) [Fact p.Prime] {X S₀ : Scheme.{u}}
    [Scheme.IsCharP S₀ p] (x₀ : X ⟶ S₀) : frobeniusTwist p x₀ ⟶ X :=
  pullback.fst x₀ (Scheme.absoluteFrobenius p S₀)

/-- Relative Frobenius with its prime supplied explicitly. -/
abbrev frobeniusRelative (p : ℕ) [Fact p.Prime] {X S₀ : Scheme.{u}}
    [Scheme.IsCharP S₀ p] (x₀ : X ⟶ S₀) : X ⟶ frobeniusTwist p x₀ :=
  @relativeFrobenius p inferInstance X S₀ x₀ inferInstance

/-- The divided-power scheme morphism `Spec(σ) : S ⟶ S`. -/
def specSigmaHom : DividedPowerSchemeHom I I s s where
  base := Spec.map (CommRingCat.ofHom σ)
  zeroFiberMap :=
    subschemeMap I I (Spec.map (CommRingCat.ofHom σ))
      (le_map_iff_comap_le.mpr h_ideal)
  zeroFiber_comm := sorry
  base_over := h_over
  ideal_compatible := h_ideal

include hp in
/-- Local nilpotence of `p` on `X` implies the same on the Frobenius twist `X^(1)`. -/
theorem relativeFrobeniusTarget_p_nilpotent :
    ∀ U : (frobeniusTwist p x₀).affineOpens,
      IsNilpotent (p : Γ(frobeniusTwist p x₀, U)) := sorry

include h_sigma in
/-- The square `X^(1) → X` over `Spec(σ)` commutes on closed fibres. -/
theorem frobeniusTwist_over_specSigma :
    frobeniusTwistToSource p x₀ ≫ x₀ =
      frobeniusTwistOver p x₀ ≫ (specSigmaHom I s σ h_ideal h_over).zeroFiberMap := sorry

/-- Relative Frobenius lies over the identity divided-power morphism of `S`. -/
theorem relativeFrobenius_over_id :
    frobeniusRelative p x₀ ≫ frobeniusTwistOver p x₀ =
      x₀ ≫ (idDividedPowerSchemeHom I s).zeroFiberMap := sorry

include hPD in
/-- Divided-power compatibility supplied for the same endomorphism on affine opens. -/
theorem specSigmaHom_dividedPowers_compatible :
    ∀ (V W : (Spec (.of A)).affineOpens)
      (hVW : W.1 ≤ (specSigmaHom I s σ h_ideal h_over).base ⁻¹ᵁ V.1),
      (γS V).IsDPMorphism (γS W) ((specSigmaHom I s σ h_ideal h_over).base.appLE V W hVW).hom := sorry

include hc in
/-- Divided-power compatibility of the identity setup morphism on affine opens. -/
theorem idDividedPowerSchemeHom_dividedPowers_compatible_spec :
    ∀ (V W : (Spec (.of A)).affineOpens)
      (hVW : W.1 ≤ (idDividedPowerSchemeHom I s).base ⁻¹ᵁ V.1),
      (γS V).IsDPMorphism (γS W)
        ((idDividedPowerSchemeHom I s).base.appLE V W hVW).hom := sorry

/-- Absolute Frobenius on `X` with the characteristic induced by `X ⟶ S₀`. -/
abbrev absoluteFrobeniusMap (p : ℕ) [Fact p.Prime]
    {X S₀ : Scheme.{u}} [Scheme.IsCharP S₀ p] (x₀ : X ⟶ S₀) : X ⟶ X :=
  @Scheme.absoluteFrobenius p inferInstance X (isCharP_of_target x₀)

/-- The relative-Frobenius and σ-twist geometric maps compose to absolute Frobenius. -/
theorem relativeFrobenius_comp :
    frobeniusRelative p x₀ ≫ frobeniusTwistToSource p x₀ =
      absoluteFrobeniusMap p x₀ := sorry

end FrobeniusSections

open FrobeniusSections

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
      (frobeniusTwistOver p x₀) x₀ (frobeniusTwistToSource p x₀) (specSigmaHom I s σ h_ideal h_over)
      (frobeniusTwist_over_specSigma I x₀ s σ h_ideal h_over h_sigma)
      (relativeFrobeniusTarget_p_nilpotent I x₀ hp) hp
      (specSigmaHom_dividedPowers_compatible I γS s σ h_ideal h_over hPD)).toRelativeFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (RelativeCRIS (Spec (.of A)) I γS hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (@CrystallineFunctor.of p inferInstance _ _ I I γS γS hc hc s s _ _
      x₀ (frobeniusTwistOver p x₀) (frobeniusRelative p x₀) (idDividedPowerSchemeHom I s)
      (relativeFrobenius_over_id I x₀ s) hp
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

namespace FrobeniusSections

/-- The small crystalline ringed morphism induced by `X^(1) ⟶ X` over `Spec(σ)`. -/
abbrev sigmaTwistMorphism :
    RingedSite.ToposHom
      (liftedRingedSite I γS hc (frobeniusTwistOver p x₀) p s
        (relativeFrobeniusTarget_p_nilpotent I x₀ hp))
      (liftedRingedSite I γS hc x₀ p s hp) :=
  smallRingedMorphism I γS hc (frobeniusTwistOver p x₀) I γS hc s s x₀
    (frobeniusTwistToSource p x₀) (specSigmaHom I s σ h_ideal h_over)
    (frobeniusTwist_over_specSigma I x₀ s σ h_ideal h_over h_sigma)
    (relativeFrobeniusTarget_p_nilpotent I x₀ hp) hp
    (specSigmaHom_dividedPowers_compatible I γS s σ h_ideal h_over hPD)

/-- The small crystalline ringed morphism induced by relative Frobenius over `id_S`. -/
abbrev relativeFrobeniusRingedMorphism :
    RingedSite.ToposHom
      (liftedRingedSite I γS hc x₀ p s hp)
      (liftedRingedSite I γS hc (frobeniusTwistOver p x₀) p s
        (relativeFrobeniusTarget_p_nilpotent I x₀ hp)) :=
  smallRingedMorphism I γS hc x₀ I γS hc s s (frobeniusTwistOver p x₀)
    (frobeniusRelative p x₀) (idDividedPowerSchemeHom I s)
    (relativeFrobenius_over_id I x₀ s) hp
    (relativeFrobeniusTarget_p_nilpotent I x₀ hp)
    (idDividedPowerSchemeHom_dividedPowers_compatible_spec I γS hc s)

end FrobeniusSections

variable [(SheafOfModules.restrictScalars
  (sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD).structureMap).IsRightAdjoint]
variable [HasModulePullbackDerived
  (sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD)]
variable [(SheafOfModules.restrictScalars
  (relativeFrobeniusRingedMorphism I γS hc x₀ s hp).structureMap).IsRightAdjoint]
variable [HasModulePullbackDerived (relativeFrobeniusRingedMorphism I γS hc x₀ s hp)]
variable [HasModulePushforwardDerived (relativeFrobeniusRingedMorphism I γS hc x₀ s hp)]
variable [HasModuleDerivedAdjunction (relativeFrobeniusRingedMorphism I γS hc x₀ s hp)]

variable (E : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
variable [SectionsCoherent I γS hc x₀ E] [CrisModuleSheaf.IsCrystal E]

namespace FrobeniusSections

/-- The σ-twisted original crystal on `Cris(X^(1)/S)`, in the derived category. -/
abbrev sigmaTwistedCrystal :=
  (sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD).modulePullbackDerived.obj
    (derivedOfCrystal I γS hc x₀ p s hp E)

/-- Absolute crystalline Frobenius pullback is the successive pullback along
`X^(1) ⟶ X` over `Spec(σ)` and `F_{X/S₀}` over `id_S`. -/
abbrev absoluteFrobeniusCrystal :=
  (relativeFrobeniusRingedMorphism I γS hc x₀ s hp).modulePullbackDerived.obj
    (sigmaTwistedCrystal I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD E)

/-- The identity divided-power base morphism acts identically on base functions. -/
theorem identityBaseRingMap_eq :
    baseRingMap (idDividedPowerSchemeHom I s).base = RingHom.id (baseRing (Spec (.of A))) := sorry

/-- Canonical elimination of derived restriction along the identity base map. -/
def identityRestrictionIso :
    ModuleCat.derivedRestrictionOfScalars (baseRingMap (idDividedPowerSchemeHom I s).base) ≅
      𝟭 (DerivedCategory (ModuleCat.{u + 1} (baseRing (Spec (.of A))))) :=
  Localization.liftNatIso
    (DerivedCategory.Q : CochainComplex (ModuleCat.{u + 1} (baseRing (Spec (.of A)))) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} (baseRing (Spec (.of A)))) (up ℤ))
    ((ModuleCat.restrictScalars (baseRingMap (idDividedPowerSchemeHom I s).base)).mapHomologicalComplex
      (up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q
    (ModuleCat.derivedRestrictionOfScalars (baseRingMap (idDividedPowerSchemeHom I s).base))
    (𝟭 (DerivedCategory (ModuleCat.{u + 1} (baseRing (Spec (.of A))))))
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (ModuleCat.restrictScalarsId' (baseRingMap (idDividedPowerSchemeHom I s).base)
          (identityBaseRingMap_eq I s)) (up ℤ)) DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q)

end FrobeniusSections

/-- 60.26.4.2: relative-Frobenius pullback
`RΓ(Cris(X^(1)/S), E^(1)) ⟶ RΓ(Cris(X/S), (F_X)_cris^* E)`,
with the σ-twist of the original crystal as input and the identity map on the
 divided-power base. -/
@[stacks 07N6]
def relativeFrobeniusDerivedGlobalSections :
    (baseDerivedGlobalSections I γS hc (frobeniusTwistOver p x₀) p s
      (relativeFrobeniusTarget_p_nilpotent I x₀ hp)).obj
        (sigmaTwistedCrystal I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD E) ⟶
    (baseDerivedGlobalSections I γS hc x₀ p s hp).obj
      (absoluteFrobeniusCrystal I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD E) :=
  (ModuleCat.derivedExtensionRestrictionAdjunction
    (baseRingMap (idDividedPowerSchemeHom I s).base)).homEquiv _ _
      (cohomologyBaseChange I γS hc x₀ I γS hc s s (frobeniusTwistOver p x₀)
        (frobeniusRelative p x₀) (idDividedPowerSchemeHom I s)
        (relativeFrobenius_over_id I x₀ s) hp
        (relativeFrobeniusTarget_p_nilpotent I x₀ hp)
        (idDividedPowerSchemeHom_dividedPowers_compatible_spec I γS hc s)
        (sigmaTwistedCrystal I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD E)) ≫
    (identityRestrictionIso I s).hom.app _

/-- The relative-Frobenius arrow is the identity-base specialization of
crystalline cohomology base change, with its scalar adjunction unfolded. -/
theorem relativeFrobeniusDerivedGlobalSections_eq :
    relativeFrobeniusDerivedGlobalSections I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD E =
      (ModuleCat.derivedExtensionRestrictionAdjunction
        (baseRingMap (idDividedPowerSchemeHom I s).base)).homEquiv _ _
          (cohomologyBaseChange I γS hc x₀ I γS hc s s (frobeniusTwistOver p x₀)
            (frobeniusRelative p x₀) (idDividedPowerSchemeHom I s)
            (relativeFrobenius_over_id I x₀ s) hp
            (relativeFrobeniusTarget_p_nilpotent I x₀ hp)
            (idDividedPowerSchemeHom_dividedPowers_compatible_spec I γS hc s)
            (sigmaTwistedCrystal I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD E)) ≫
        (identityRestrictionIso I s).hom.app _ := sorry
