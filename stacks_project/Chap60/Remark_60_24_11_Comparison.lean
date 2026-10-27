/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Crystalline.SmoothLift.Cohomology
public import stacks_project.Chap60.Proposition_60_21_1
import StacksCheckRecall

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients
universe u

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

variable (U : Y.affineOpens)

/- Remark 60.24.11 (Comparison) (1): the base divided powers extend to the closed fibre's ideal. -/
@[stacks 07MW] #check (AlgebraicGeometry.Scheme.Crystalline.smoothLiftDividedPowers_spec γA f I hI U :
  DividedPowers.IsDPMorphism γA (smoothLiftDividedPowers γA f I hI U)
    (Scheme.Hom.sectionsMap f U))

/- Remark 60.24.11 (Comparison) (2): the canonical ordinary connection is integrable. -/
@[stacks 07MW] #check (AlgebraicGeometry.Scheme.Crystalline.SmoothLift.connection_integrable
  γA f I γS hc hI hγ hpnil F :
    AlgebraicGeometry.Scheme.Crystalline.SmoothLift.connection γA f I γS hc hI hγ hpnil F ≫
      (AlgebraicGeometry.Scheme.Modules.DeRham.baseDegreeOne f
        (AlgebraicGeometry.Scheme.Crystalline.SmoothLift.coefficient γA f I γS hc hI hγ hpnil F)).inv ≫
      AlgebraicGeometry.Scheme.Crystalline.SmoothLift.Affine.sheafDifferential γA f I γS hc hI hγ hpnil F 1 = 0)

variable (s : Spec (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1}
      (liftedRingedSite I γS hc (smoothLift_x₀ f I) p s (smoothLift_p_nilpotent f I hpnil)))]
    [HasSheafify (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian (Sheaf (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A))]

/- Remark 60.24.11 (Comparison) (3): crystalline and smooth-lift de Rham derived sections agree in D(A). -/
@[stacks 07MW] #check (AlgebraicGeometry.Scheme.Crystalline.SmoothLift.crystalline_deRham_comparison
  γA f I γS hc hI hγ hpnil F s :
    IsIsomorphic (AlgebraicGeometry.Scheme.Crystalline.SmoothLift.crystallineSections f I γS hc hpnil F s)
      (AlgebraicGeometry.Scheme.Crystalline.SmoothLift.deRhamSections γA f I γS hc hI hγ hpnil F))
