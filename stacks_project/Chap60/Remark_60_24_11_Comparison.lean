/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import stacks_project.Chap60.Remark_60_24_11_Comparison_Object
public import stacks_project.Chap60.Remark_60_24_11_Comparison_SmoothLiftGeometry
public import stacks_project.Chap60.Remark_60_24_11_Comparison_DeRham
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineDifferentials
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffinePDForms
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineTensorSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineSheafExtension
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineGeometry
public import stacks_project.Chap60.Remark_60_24_11_Comparison_ModuleDerivedSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_SheafDegreeBridges
public import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients
universe u
namespace CrystallineSmoothLiftComparison

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [Smooth f]
variable (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
variable (hpnil : IsNilpotent (p : A))
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc (smoothLift f I) (smoothLift_x₀ f I))
variable [SectionsCoherent I γS hc (smoothLift_x₀ f I) F]
variable [CrisModuleSheaf.IsCrystal F] [CrisModuleSheaf.IsLocallyQuasiCoherent F]

/-- The source connection on F_Y is the actual degree-zero sheaf
differential, transported only through canonical exterior-degree identifications. -/
noncomputable def connection :
    CrystallineSmoothLiftTerms.asBaseSheaf f
        (CrystallineSmoothLiftRepair.coefficient γA f I γS hc hI hγ hpnil F) ⟶
      CrystallineSmoothLiftTerms.asBaseSheaf f
        (CrystallineSmoothLiftTerms.oneFormTensor f
          (CrystallineSmoothLiftRepair.coefficient γA f I γS hc hI hγ hpnil F)) :=
  (CrystallineSheafDegreeBridges.baseDegreeZero f
      (CrystallineSmoothLiftRepair.coefficient γA f I γS hc hI hγ hpnil F)).inv ≫
    CrystallineSmoothLiftAffine.sheafDifferential γA f I γS hc hI hγ hpnil F 0 ≫
      (CrystallineSheafDegreeBridges.baseDegreeOne f
        (CrystallineSmoothLiftRepair.coefficient γA f I γS hc hI hγ hpnil F)).hom

/-- Remark 60.24.11 (Comparison) (1): the given divided powers extend to
the actual ideal of the closed fibre X in the smooth lift Y. -/
@[stacks 07MW]
theorem dividedPowers_extend (U : Y.affineOpens) :
    DividedPowers.IsDPMorphism γA (smoothLiftDividedPowers γA f I hI U)
      (affineSectionMap f U) := sorry

/-- Remark 60.24.11 (Comparison) (2): the actual canonical connection on
F_Y is integrable; its curvature vanishes in the genuine sheaf de Rham complex. -/
@[stacks 07MW]
theorem connection_integrable :
    connection γA f I γS hc hI hγ hpnil F ≫
      (CrystallineSheafDegreeBridges.baseDegreeOne f
        (CrystallineSmoothLiftRepair.coefficient γA f I γS hc hI hγ hpnil F)).inv ≫
      CrystallineSmoothLiftAffine.sheafDifferential γA f I γS hc hI hγ hpnil F 1 = 0 := sorry

variable (s : Spec (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))

/-- The crystalline side is derived global sections of the actual
coherent crystal, with its base action restricted along the canonical map
A → ULift Γ(Spec A). No terminal crystalline-site object is required. -/
noncomputable def crystallineSections
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1}
      (liftedRingedSite I γS hc (smoothLift_x₀ f I) p s (smoothLift_p_nilpotent f I hpnil)))] :
    DerivedCategory (ModuleCat.{u + 1} A) :=
  (CrystallineModuleDerivedSections.baseRestriction A).obj
    ((baseDerivedGlobalSections I γS hc (smoothLift_x₀ f I) p s
      (smoothLift_p_nilpotent f I hpnil)).obj
      (derivedOfCrystal I γS hc (smoothLift_x₀ f I) p s (smoothLift_p_nilpotent f I hpnil) F))

/-- The smooth-lift side is genuine derived global sections of the
constructed de Rham complex of A-module sheaves on all of Y. -/
noncomputable def deRhamSections
    [HasSheafify (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian (Sheaf (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A))] :
    DerivedCategory (ModuleCat.{u + 1} A) :=
  CrystallineModuleDerivedSections.ofComplex A Y
    (CrystallineSmoothLiftAffine.sheafComplex γA f I γS hc hI hγ hpnil F)

/-- Remark 60.24.11 (Comparison) (3): for the smooth lift of X over the
p-nilpotent divided-power base, crystalline RΓ(F) is isomorphic in D(A) to
RΓ(Y, F_Y ⊗ Ω^•_{Y/S}) with its actual crystal-induced connection. -/
@[stacks 07MW]
theorem crystalline_deRham_comparison
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1}
      (liftedRingedSite I γS hc (smoothLift_x₀ f I) p s (smoothLift_p_nilpotent f I hpnil)))]
    [HasSheafify (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian (Sheaf (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A))] :
    IsIsomorphic (crystallineSections f I γS hc hpnil F s)
      (deRhamSections γA f I γS hc hI hγ hpnil F) := sorry

end CrystallineSmoothLiftComparison
