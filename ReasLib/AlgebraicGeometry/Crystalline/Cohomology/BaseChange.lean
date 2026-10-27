/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.RingedMorphism.Relative
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf CrystallineCoefficients

universe u

namespace CrystallineRingedGeometry

variable {S X S' X' : Scheme.{u}} {p : ℕ} [Fact p.Prime]
variable (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : S.affineOpens) (a : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen a))
    (S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom)
variable (x₀ : X ⟶ I.subscheme)
variable (I' : S'.IdealSheafData)
variable (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
variable (hc' : ∀ (V : S'.affineOpens) (a : Γ(S', V)),
  (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen a))
    (S'.presheaf.map (homOfLE (S'.basicOpen_le a)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (x'₀ : X' ⟶ I'.subscheme) (f : X ⟶ X')
variable (g : DividedPowerSchemeHom I I' s s') (hf : f ≫ x'₀ = x₀ ≫ g.zeroFiberMap)
variable (hpX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (hpX' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))
variable (hγ : ∀ (V : S'.affineOpens) (W : S.affineOpens)
  (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
  (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom)

variable [HasSheafify (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1))]
variable [HasSheafify (crystallineZariskiTopology S' I' γ' hc' X' x'₀) (Type (u + 1))]
variable [HasSheafify (smallCrystallineTopology p S I γ hc s X x₀ hpX) (Type (u + 1))]
variable [HasSheafify (smallCrystallineTopology p S' I' γ' hc' s' X' x'₀ hpX') (Type (u + 1))]
variable [(crystallineZariskiTopology S I γ hc X x₀).HasSheafCompose (forget RingCat.{u + 1})]
variable [(crystallineZariskiTopology S' I' γ' hc' X' x'₀).HasSheafCompose (forget RingCat.{u + 1})]
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

/-- Derived sections of a crystalline direct image identify with scalar-restricted sections. -/
noncomputable def crystallineDerivedGlobalSectionsIso :
    RingedSite.ToposHom.sectionsSourceDerived.{u + 1, u, u + 1, u, u + 1} (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ) ≅
      RingedSite.ToposHom.sectionsTargetDerived.{u + 1, u, u + 1, u, u + 1} (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ) :=
  RingedSite.ToposHom.derivedGlobalSectionsPushforwardIso (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)

/-- The actual crystalline base actions identify iterated scalar restrictions. -/
noncomputable def crystallineBaseRestrictionIso :=
  RingedSite.ToposHom.baseRestrictionIso (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)
    (CrystallineCoefficients.baseToGlobalSections I' γ' hc' x'₀ p s' hpX') (CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX)
    (CrystallineCoefficients.baseRingMap g.base) (baseActions_compatible I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)

/-- Crystalline cohomology base change is the scalar adjoint transpose of derived pullback. -/
noncomputable def cohomologyBaseChange
    (K : RingedSite.Hom.ModuleDerived.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX')) :=
  RingedSite.ToposHom.baseScalarComparison (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)
    (CrystallineCoefficients.baseToGlobalSections I' γ' hc' x'₀ p s' hpX') (CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX)
    (CrystallineCoefficients.baseRingMap g.base) (baseActions_compatible I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ) K

/-- Crystalline cohomology commutes with base change for flat quasi-coherent crystals
along a cartesian Tor-independent square whose target closed-fibre morphism is
quasi-compact, quasi-separated and a local complete intersection, when the prime
is nilpotent on the affine divided-power base. -/
theorem cohomologyBaseChange_isIso
    [IsAffine S] [IsAffine S']
    [I.toModule.IsQuasicoherent] [I'.toModule.IsQuasicoherent]
    [QuasiCompact x'₀] [QuasiSeparated x'₀]
    [LocallyOfType RingHom.IsLocalCompleteIntersection x'₀]
    [Fact (IsNilpotent (p : Γ(S', ⊤)))]
    [Fact (IsPullback f x₀ x'₀ g.zeroFiberMap)]
    [Fact (Scheme.TorIndependentOver (Over.mk x'₀) (Over.mk g.zeroFiberMap))]
    (F' : CrisModuleSheaf S' I' γ' hc' X' x'₀)
    [CrisModuleSheaf.IsCrystal F'] [CrisModuleSheaf.IsLocallyQuasiCoherent F']
    [∀ T, SheafOfModules.IsFlat (F'.obj T)] :
    IsIso (RingedSite.ToposHom.baseScalarComparisonToOrdinary
      (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)
      (CrystallineCoefficients.baseToGlobalSections I' γ' hc' x'₀ p s' hpX') (CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX)
      (CrystallineCoefficients.baseRingMap g.base) (baseActions_compatible I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)
      (liftedOfCrystal I' γ' hc' x'₀ F' p s' hpX')) := sorry

end CrystallineRingedGeometry
