/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.RingedMorphism.Relative
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline CrystallineCoefficients

universe u

namespace CrystallineRingedGeometry

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

/-- The crystalline cohomology base-change map with arbitrary ordinary module coefficients and their ordinary pullback. -/
noncomputable def crystallineCohomologyBaseChange
    [IsAffine S] [IsAffine S']
    (F' : RingedSite.ModuleCat.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX')) :=
  RingedSite.ToposHom.baseScalarComparisonToOrdinary
    (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)
    (CrystallineCoefficients.baseToGlobalSections I' γ' hc' x'₀ p s' hpX')
    (CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX)
    (CrystallineCoefficients.baseRingMap g.base)
    (baseActions_compatible I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ) F'

/-- Crystalline cohomology base change is the scalar comparison followed by derived sections of the ordinary-coefficient counit. -/
theorem crystallineCohomologyBaseChange_spec [IsAffine S] [IsAffine S']
    (F' : RingedSite.ModuleCat.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' x'₀ p s' hpX')) :
    crystallineCohomologyBaseChange I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ F' =
      RingedSite.ToposHom.baseScalarComparisonToOrdinary
        (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ)
        (CrystallineCoefficients.baseToGlobalSections I' γ' hc' x'₀ p s' hpX')
        (CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX)
        (CrystallineCoefficients.baseRingMap g.base)
        (baseActions_compatible I γ hc x₀ I' γ' hc' s s' x'₀ f g hf hpX hpX' hγ) F' := sorry

end CrystallineRingedGeometry
