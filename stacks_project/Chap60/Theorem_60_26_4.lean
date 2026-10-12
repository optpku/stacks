/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Definition_60_26_2
public import stacks_project.Chap60.«60_26_4_2»
public import stacks_project.Chap60.«60_26_4_3»
public import stacks_project.Chap60.Remark_60_24_12_Perfectness
public import stacks_project.Chap60.Remark_60_24_9_Base_change_isomorphism_RingedGeometry
public import stacks_project.Chap60.Lemma_60_25_4_Linearization
public import stacks_project.Chap60.Lemma_60_25_6_RelativeFrobenius
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Composition
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Tactic.CrossRefAttribute

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients CrystallineRingedGeometry SheafOfModules
open CrystallineModuleDerivedSections
open RingedSite.ToposHom
open Scheme.IdealSheafData CategoryTheory.ModuleCat.DerivedExtension

universe u

@[expose] public section

noncomputable section

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

include h_ideal in
/-- The supplied ideal-preservation evidence for the specified endomorphism. -/
theorem specSigmaHom_ideal_compatible :
    I.comap (Spec.map (CommRingCat.ofHom σ)) ≤ I :=
  sorry

/-- The divided-power scheme morphism `Spec(σ) : S ⟶ S`. -/
def specSigmaHom : DividedPowerSchemeHom I I s s where
  base := Spec.map (CommRingCat.ofHom σ)
  zeroFiberMap :=
    subschemeMap I I (Spec.map (CommRingCat.ofHom σ))
      (le_map_iff_comap_le.mpr h_ideal)
  zeroFiber_comm := sorry
  base_over := h_over
  ideal_compatible := h_ideal

/-- `specSigmaHom` is induced by `σ` on underlying schemes. -/
theorem specSigmaHom_base :
    (specSigmaHom I s σ h_ideal h_over).base = Spec.map (CommRingCat.ofHom σ) :=
  sorry

include h_sigma in
/-- On closed fibres, `Spec(σ)` induces the absolute Frobenius of `S₀`. -/
theorem specSigmaHom_zeroFiber :
    (specSigmaHom I s σ h_ideal h_over).zeroFiberMap = Scheme.absoluteFrobenius p I.subscheme :=
  sorry

include hp in
/-- Local nilpotence of `p` on `X` implies the same on the Frobenius twist `X^(1)`. -/
theorem relativeFrobeniusTarget_p_nilpotent :
    ∀ U : (frobeniusTwist p x₀).affineOpens,
      IsNilpotent (p : Γ(frobeniusTwist p x₀, U)) :=
  sorry

include h_sigma in
/-- The square `X^(1) → X` over `Spec(σ)` commutes on closed fibres. -/
theorem frobeniusTwist_over_specSigma :
    frobeniusTwistToSource p x₀ ≫ x₀ =
      frobeniusTwistOver p x₀ ≫ (specSigmaHom I s σ h_ideal h_over).zeroFiberMap :=
  sorry

/-- Relative Frobenius lies over the identity divided-power morphism of `S`. -/
theorem relativeFrobenius_over_id :
    frobeniusRelative p x₀ ≫ frobeniusTwistOver p x₀ =
      x₀ ≫ (idDividedPowerSchemeHom I s).zeroFiberMap :=
  sorry

include hPD in
/-- Divided-power compatibility supplied for the same endomorphism on affine opens. -/
theorem specSigmaHom_dividedPowers_compatible :
    ∀ (V W : (Spec (.of A)).affineOpens)
      (hVW : W.1 ≤ (specSigmaHom I s σ h_ideal h_over).base ⁻¹ᵁ V.1),
      (γS V).IsDPMorphism (γS W) ((specSigmaHom I s σ h_ideal h_over).base.appLE V W hVW).hom :=
  sorry

include hc in
/-- Divided-power compatibility of the identity setup morphism on affine opens. -/
theorem idDividedPowerSchemeHom_dividedPowers_compatible_spec :
    ∀ (V W : (Spec (.of A)).affineOpens)
      (hVW : W.1 ≤ (idDividedPowerSchemeHom I s).base ⁻¹ᵁ V.1),
      (γS V).IsDPMorphism (γS W)
        ((idDividedPowerSchemeHom I s).base.appLE V W hVW).hom :=
  sorry

/-- Identity then `Spec(σ)` on base rings is `Spec(σ)`. -/
theorem baseRingMap_id_comp :
    (baseRingMap (idDividedPowerSchemeHom I s).base).comp
        (baseRingMap (specSigmaHom I s σ h_ideal h_over).base) =
      baseRingMap (specSigmaHom I s σ h_ideal h_over).base :=
  sorry

/-- Iterated derived extension along `Spec(σ)` then `id_S` is extension along the composite. -/
def sigmaIdExtensionIso :
    ModuleCat.derivedExtensionOfScalars.{u + 1, u + 1, u + 1}
        (baseRingMap (specSigmaHom I s σ h_ideal h_over).base) ⋙
      ModuleCat.derivedExtensionOfScalars.{u + 1, u + 1, u + 1}
        (baseRingMap (idDividedPowerSchemeHom I s).base) ≅
      ModuleCat.derivedExtensionOfScalars.{u + 1, u + 1, u + 1}
        ((baseRingMap (idDividedPowerSchemeHom I s).base).comp
          (baseRingMap (specSigmaHom I s σ h_ideal h_over).base)) :=
  Composition.iso.{u + 1, u + 1}
      (baseRingMap (specSigmaHom I s σ h_ideal h_over).base)
      (baseRingMap (idDividedPowerSchemeHom I s).base)

/-- `sigmaIdExtensionIso` is the derived-extension composition isomorphism. -/
theorem sigmaIdExtensionIso_eq :
    sigmaIdExtensionIso I s σ h_ideal h_over =
      Composition.iso.{u + 1, u + 1}
          (baseRingMap (specSigmaHom I s σ h_ideal h_over).base)
          (baseRingMap (idDividedPowerSchemeHom I s).base) :=
  sorry

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

variable [(SheafOfModules.restrictScalars
  (sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD).structureMap).IsRightAdjoint]
variable [HasModulePullbackDerived (sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD)]
variable [HasModulePushforwardDerived (sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD)]
variable [HasModuleDerivedAdjunction (sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD)]
variable [(SheafOfModules.restrictScalars
  (relativeFrobeniusRingedMorphism I γS hc x₀ s hp).structureMap).IsRightAdjoint]
variable [HasModulePullbackDerived (relativeFrobeniusRingedMorphism I γS hc x₀ s hp)]
variable [HasModulePushforwardDerived (relativeFrobeniusRingedMorphism I γS hc x₀ s hp)]
variable [HasModuleDerivedAdjunction (relativeFrobeniusRingedMorphism I γS hc x₀ s hp)]

variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
variable [SectionsCoherent I γS hc x₀ F] [CrisModuleSheaf.IsCrystal F]

/-- 60.26.4.1: the `σ`-specialization of crystalline cohomology base change. -/
def sigmaBaseChange :=
  cohomologyBaseChange I γS hc (frobeniusTwistOver p x₀) I γS hc s s x₀
    (frobeniusTwistToSource p x₀) (specSigmaHom I s σ h_ideal h_over)
    (frobeniusTwist_over_specSigma I x₀ s σ h_ideal h_over h_sigma)
    (relativeFrobeniusTarget_p_nilpotent I x₀ hp) hp
    (specSigmaHom_dividedPowers_compatible I γS s σ h_ideal h_over hPD)
    (derivedOfCrystal I γS hc x₀ p s hp F)

/-- `sigmaBaseChange` is `cohomologyBaseChange` along `Spec(σ)`. -/
theorem sigmaBaseChange_eq :
    sigmaBaseChange I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F =
      cohomologyBaseChange I γS hc (frobeniusTwistOver p x₀) I γS hc s s x₀
        (frobeniusTwistToSource p x₀) (specSigmaHom I s σ h_ideal h_over)
        (frobeniusTwist_over_specSigma I x₀ s σ h_ideal h_over h_sigma)
        (relativeFrobeniusTarget_p_nilpotent I x₀ hp) hp
        (specSigmaHom_dividedPowers_compatible I γS s σ h_ideal h_over hPD)
        (derivedOfCrystal I γS hc x₀ p s hp F) :=
  sorry

/-- 60.26.4.2: crystalline cohomology base change along relative Frobenius. -/
def relativeFrobeniusBaseChange :=
  cohomologyBaseChange I γS hc x₀ I γS hc s s (frobeniusTwistOver p x₀)
    (frobeniusRelative p x₀) (idDividedPowerSchemeHom I s)
    (relativeFrobenius_over_id I x₀ s) hp
    (relativeFrobeniusTarget_p_nilpotent I x₀ hp)
    (idDividedPowerSchemeHom_dividedPowers_compatible_spec I γS hc s)
    ((sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD).modulePullbackDerived.obj
      (derivedOfCrystal I γS hc x₀ p s hp F))

/-- `relativeFrobeniusBaseChange` is `cohomologyBaseChange` along `F_{X/S₀}`. -/
theorem relativeFrobeniusBaseChange_eq :
    relativeFrobeniusBaseChange I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F =
      cohomologyBaseChange I γS hc x₀ I γS hc s s (frobeniusTwistOver p x₀)
        (frobeniusRelative p x₀) (idDividedPowerSchemeHom I s)
        (relativeFrobenius_over_id I x₀ s) hp
        (relativeFrobeniusTarget_p_nilpotent I x₀ hp)
        (idDividedPowerSchemeHom_dividedPowers_compatible_spec I γS hc s)
        ((sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD).modulePullbackDerived.obj
          (derivedOfCrystal I γS hc x₀ p s hp F)) :=
  sorry

/-- The crystalline Frobenius pullback `(F_X)_cris^* ℰ` as a derived crystal. -/
def crystallineFrobeniusPullback :
    RingedSite.Hom.ModuleDerived.{u + 1} (liftedRingedSite I γS hc x₀ p s hp) :=
  (relativeFrobeniusRingedMorphism I γS hc x₀ s hp).modulePullbackDerived.obj
    ((sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD).modulePullbackDerived.obj
      (derivedOfCrystal I γS hc x₀ p s hp F))

/-- `(F_X)_cris^*` is relative-Frobenius pullback of the `Spec(σ)`-twist. -/
theorem crystallineFrobeniusPullback_eq :
    crystallineFrobeniusPullback I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F =
      (relativeFrobeniusRingedMorphism I γS hc x₀ s hp).modulePullbackDerived.obj
        ((sigmaTwistMorphism I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD).modulePullbackDerived.obj
          (derivedOfCrystal I γS hc x₀ p s hp F)) :=
  sorry

/-- 60.26.4.3: derived global sections of the coefficient Frobenius `F_ℰ`. -/
def coefficientFrobenius
    (F_E : crystallineFrobeniusPullback I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F ⟶
        derivedOfCrystal I γS hc x₀ p s hp F) :=
  (baseDerivedGlobalSections I γS hc x₀ p s hp).map F_E

/-- `coefficientFrobenius` is `rGamma.map F_ℰ`. -/
theorem coefficientFrobenius_eq
    (F_E : crystallineFrobeniusPullback I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F ⟶
        derivedOfCrystal I γS hc x₀ p s hp F) :
    coefficientFrobenius I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F F_E =
      (baseDerivedGlobalSections I γS hc x₀ p s hp).map F_E :=
  sorry

/-- The coefficient Frobenius is nondegenerate when some power of `p` factors
through a Verschiebung. -/
def frobeniusMorphism_isNondegenerate
    {K K' : RingedSite.Hom.ModuleDerived.{u + 1} (liftedRingedSite I γS hc x₀ p s hp)}
    (F_E : K' ⟶ K) : Prop :=
  ∃ i : ℕ, ∃ V : K ⟶ K', F_E ≫ V = (p ^ i) • 𝟙 K'

/-- Nondegeneracy unfolds to the existence of a Verschiebung for a power of `p`. -/
theorem frobeniusMorphism_isNondegenerate_iff
    {K K' : RingedSite.Hom.ModuleDerived.{u + 1} (liftedRingedSite I γS hc x₀ p s hp)}
    (F_E : K' ⟶ K) :
    frobeniusMorphism_isNondegenerate I γS hc x₀ s hp F_E ↔
      ∃ i : ℕ, ∃ V : K ⟶ K', F_E ≫ V = (p ^ i) • 𝟙 K' :=
  sorry

/-- The canonical crystalline-cohomology Frobenius action
`F_ℰ ∘ (F_X)_cris^*`, as the composite of the σ-base-change arrow
60.26.4.1, the relative-Frobenius comparison 60.26.4.2, and the
coefficient Frobenius 60.26.4.3, transported to `D(A)`. -/
def frobeniusCohomologyMap
    (F_E : crystallineFrobeniusPullback I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F ⟶
        derivedOfCrystal I γS hc x₀ p s hp F) :=
  (baseRestriction A).map
    ((sigmaIdExtensionIso I s σ h_ideal h_over).inv.app _ ≫
      (ModuleCat.derivedExtensionOfScalars
          (baseRingMap (idDividedPowerSchemeHom I s).base)).map
        (sigmaBaseChange I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F) ≫
      relativeFrobeniusBaseChange I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F ≫
      coefficientFrobenius I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F F_E)

/-- The canonical map is the composite of the 60.26.4.1 σ-base-change,
the relative-Frobenius comparison, and the coefficient Frobenius,
after restriction of scalars to `D(A)`. -/
theorem frobeniusCohomologyMap_comp
    (F_E : crystallineFrobeniusPullback I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F ⟶
        derivedOfCrystal I γS hc x₀ p s hp F) :
    frobeniusCohomologyMap I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F F_E =
      (baseRestriction A).map
        ((sigmaIdExtensionIso I s σ h_ideal h_over).inv.app _ ≫
          (ModuleCat.derivedExtensionOfScalars
              (baseRingMap (idDividedPowerSchemeHom I s).base)).map
            (sigmaBaseChange I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F) ≫
          relativeFrobeniusBaseChange I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F ≫
          coefficientFrobenius I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F F_E) :=
  sorry

/-- Theorem 60.26.4: in Situation 60.26.1, for a nondegenerate `F`-crystal
`(ℰ, F_ℰ)`, if `A` is a `p`-adically complete Noetherian ring and
`X ⟶ S₀` is proper smooth, then the canonical map
`F_ℰ ∘ (F_X)_cris^* : RΓ(Cris(X/S), ℰ) ⊗^L[A,σ] A ⟶ RΓ(Cris(X/S), ℰ)`
becomes an isomorphism after inverting `p`. -/
@[stacks 07N5]
theorem frobeniusCohomologyMap_isIso_after_inverting_p
    (F_E : crystallineFrobeniusPullback I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F ⟶
        derivedOfCrystal I γS hc x₀ p s hp F)
    [IsAdicComplete (Ideal.span {(p : A)}) A] [IsNoetherianRing A]
    [IsProper x₀] [Smooth x₀]
    [HasWeakSheafify
      (smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp) AddCommGrpCat.{u}]
    [(smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite (Spec (.of A)) I γS hc X x₀,
      HasWeakSheafify
        ((smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp).over U)
        AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite (Spec (.of A)) I γS hc X x₀,
      ((smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀ hp).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u}]
    [IsCrystalInFiniteLocallyFreeModules (ofCrystal I γS hc x₀ F p s hp)]
    (h_nondegenerate :
      frobeniusMorphism_isNondegenerate I γS hc x₀ s hp F_E) :
    IsIso ((ModuleCat.derivedExtensionOfScalars
        (algebraMap A (Localization.Away (p : A)))).map
      (frobeniusCohomologyMap I γS hc x₀ s hp σ h_ideal h_over h_sigma hPD F F_E)) :=
  sorry

end AlgebraicGeometry.Scheme.Crystalline
