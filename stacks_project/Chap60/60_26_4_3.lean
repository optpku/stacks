/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Basic
public import ReasLib.AlgebraicGeometry.Crystalline.Frobenius.Lift
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.BaseSections
public import stacks_project.Chap60.Remark_60_24_9_Base_change_isomorphism_RingedGeometry
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients CrystallineRingedGeometry
open Scheme.IdealSheafData RingedSite.ToposHom ULift

universe u

noncomputable section

namespace CrystallineCoefficient

variable {p : ℕ} [Fact p.Prime] {A : DividedPowerRing.{u}}
variable (B : FrobeniusBase p A)

/-- The divided-power base morphism induced by the given Frobenius lift. -/
def specSigmaHom :
    DividedPowerSchemeHom B.toBase.ideal B.toBase.ideal B.toBase.toSpec B.toBase.toSpec where
  base := B.sigmaMap
  zeroFiberMap := B.sigmaZeroFiber
  zeroFiber_comm := subschemeMap_subschemeι _ _ _ _
  base_over := B.sigmaMap_over
  ideal_compatible := B.sigmaMap_preservesIdeal

variable [HasSheafify
  (crystallineZariskiTopology B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.source B.toBase.sourceToClosed) (Type (u + 1))]
variable [(crystallineZariskiTopology B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
  B.toBase.compatible B.toBase.source B.toBase.sourceToClosed).HasSheafCompose
    (forget RingCat.{u + 1})]
variable [HasSheafify
  (smallCrystallineTopology p B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.toSpec B.toBase.source B.toBase.sourceToClosed
    B.toBase.prime_nilpotent) (Type (u + 1))]
variable [(smallCrystallineTopology p B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
  B.toBase.compatible B.toBase.toSpec B.toBase.source B.toBase.sourceToClosed
  B.toBase.prime_nilpotent).HasSheafCompose (forget RingCat.{u + 1})]
variable [∀ P : (RelativeCRIS B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.source B.toBase.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (CrystallineFunctor.of B.sourceFrobenius (specSigmaHom B)
    B.absoluteFrobenius_over_sigma B.toBase.prime_nilpotent B.toBase.prime_nilpotent
    B.sigma_dividedPowers).toRelativeFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.source B.toBase.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.source B.toBase.sourceToClosed).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.source B.toBase.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.source B.toBase.sourceToClosed).op.HasLeftKanExtension P]

/-- The crystalline ringed-topos endomorphism induced by absolute Frobenius and `σ`. -/
abbrev crystallineFrobeniusMorphism :=
  smallRingedMorphism B.toBase.ideal B.toBase.dividedPowers B.toBase.compatible
    B.toBase.sourceToClosed B.toBase.ideal B.toBase.dividedPowers B.toBase.compatible
    B.toBase.toSpec B.toBase.toSpec B.toBase.sourceToClosed
    B.sourceFrobenius (specSigmaHom B) B.absoluteFrobenius_over_sigma
    B.toBase.prime_nilpotent B.toBase.prime_nilpotent B.sigma_dividedPowers

variable [HasWeakSheafify
  (smallCrystallineTopology p B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.toSpec B.toBase.source B.toBase.sourceToClosed
    B.toBase.prime_nilpotent) AddCommGrpCat.{u + 1}]
variable [(smallCrystallineTopology p B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
  B.toBase.compatible B.toBase.toSpec B.toBase.source B.toBase.sourceToClosed
  B.toBase.prime_nilpotent).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable (E : CrisModuleSheaf B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
  B.toBase.compatible B.toBase.source B.toBase.sourceToClosed)
variable [SectionsCoherent B.toBase.ideal B.toBase.dividedPowers B.toBase.compatible
  B.toBase.sourceToClosed E] [CrisModuleSheaf.IsCrystal E]

/-- The ordinary crystalline Frobenius pullback of the lifted crystal coefficient. -/
def crystallineFrobeniusPullback :=
  (crystallineFrobeniusMorphism B).modulePullback.obj
    (liftedOfCrystal B.toBase.ideal B.toBase.dividedPowers B.toBase.compatible
      B.toBase.sourceToClosed E p B.toBase.toSpec B.toBase.prime_nilpotent)

end CrystallineCoefficient

open CrystallineCoefficient

variable {p : ℕ} [Fact p.Prime] {A : DividedPowerRing.{u}}
variable (B : FrobeniusBase p A)
variable [HasSheafify
  (crystallineZariskiTopology B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.source B.toBase.sourceToClosed) (Type (u + 1))]
variable [(crystallineZariskiTopology B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
  B.toBase.compatible B.toBase.source B.toBase.sourceToClosed).HasSheafCompose
    (forget RingCat.{u + 1})]
variable [HasSheafify
  (smallCrystallineTopology p B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.toSpec B.toBase.source B.toBase.sourceToClosed
    B.toBase.prime_nilpotent) (Type (u + 1))]
variable [(smallCrystallineTopology p B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
  B.toBase.compatible B.toBase.toSpec B.toBase.source B.toBase.sourceToClosed
  B.toBase.prime_nilpotent).HasSheafCompose (forget RingCat.{u + 1})]
variable [∀ P : (RelativeCRIS B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.source B.toBase.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (CrystallineFunctor.of B.sourceFrobenius (specSigmaHom B)
    B.absoluteFrobenius_over_sigma B.toBase.prime_nilpotent B.toBase.prime_nilpotent
    B.sigma_dividedPowers).toRelativeFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.source B.toBase.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.source B.toBase.sourceToClosed).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.source B.toBase.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.source B.toBase.sourceToClosed).op.HasLeftKanExtension P]
variable [HasSheafify
  (smallCrystallineTopology p B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.toSpec B.toBase.source B.toBase.sourceToClosed
    B.toBase.prime_nilpotent) AddCommGrpCat.{u + 1}]
variable [(smallCrystallineTopology p B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
  B.toBase.compatible B.toBase.toSpec B.toBase.source B.toBase.sourceToClosed
  B.toBase.prime_nilpotent).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable [IsGrothendieckAbelian
  (RingedSite.ModuleCat.{u + 1} (liftedRingedSite B.toBase.ideal B.toBase.dividedPowers
    B.toBase.compatible B.toBase.sourceToClosed p B.toBase.toSpec B.toBase.prime_nilpotent))]

namespace CrystallineCoefficient

/-- The presenting ring acts on crystalline functions through the actual thickening
structure maps and the affine global-sections identification. -/
def baseAction :
    ULift.{u + 1} A →+* (CategoryTheory.Limits.limit
      (liftedStructureSheaf B.toBase.ideal B.toBase.dividedPowers B.toBase.compatible
        B.toBase.sourceToClosed p B.toBase.toSpec B.toBase.prime_nilpotent).obj :
          RingCat.{u + 1}) :=
  (baseToGlobalSections B.toBase.ideal B.toBase.dividedPowers B.toBase.compatible
    B.toBase.sourceToClosed p B.toBase.toSpec B.toBase.prime_nilpotent).comp
      ((ringEquiv.symm.toRingHom).comp
        ((Scheme.Hom.appTop (eqToHom B.scheme_eq)).hom.comp
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp ringEquiv.toRingHom)))

end CrystallineCoefficient

variable (E : CrisModuleSheaf B.toBase.scheme B.toBase.ideal B.toBase.dividedPowers
  B.toBase.compatible B.toBase.source B.toBase.sourceToClosed)
variable [SectionsCoherent B.toBase.ideal B.toBase.dividedPowers B.toBase.compatible
  B.toBase.sourceToClosed E] [CrisModuleSheaf.IsCrystal E]
variable [∀ T, (E.obj T).IsFiniteLocallyFree]
variable (F_E : crystallineFrobeniusPullback B E ⟶
  liftedOfCrystal B.toBase.ideal B.toBase.dividedPowers B.toBase.compatible
    B.toBase.sourceToClosed E p B.toBase.toSpec B.toBase.prime_nilpotent)

/- 60.26.4.3: the ordinary Frobenius coefficient morphism of a finite locally free
crystal induces the A-linear arrow on derived crystalline global sections. -/
@[stacks 07QD] #check
  (SheafOfModules.BaseSections.map.{u + 1, u, u + 1, u + 1} (baseAction B) F_E :
    (SheafOfModules.BaseSections.derivedGlobalSections.{u + 1, u, u + 1, u + 1}
      (baseAction B)).obj
      ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj (crystallineFrobeniusPullback B E)) ⟶
    (SheafOfModules.BaseSections.derivedGlobalSections.{u + 1, u, u + 1, u + 1}
      (baseAction B)).obj
      ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
        (liftedOfCrystal B.toBase.ideal B.toBase.dividedPowers B.toBase.compatible
          B.toBase.sourceToClosed E p B.toBase.toSpec B.toBase.prime_nilpotent)))
