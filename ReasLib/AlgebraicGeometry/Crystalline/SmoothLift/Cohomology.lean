/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Crystalline.SmoothLift.DeRham
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.AffineBase
public import ReasLib.AlgebraicGeometry.Scheme.Module.DerivedSections
public import Mathlib.CategoryTheory.IsomorphismClasses

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients
universe u
namespace AlgebraicGeometry.Scheme.Crystalline.SmoothLift

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [Smooth f]
variable (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (hI : Scheme.Crystalline.Affine.idealCompatible IA I) (hγ : Scheme.Crystalline.Affine.dividedPowersCompatible IA γA I γS)
variable (hpnil : IsNilpotent (p : A))
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc (smoothLift f I) (smoothLift_x₀ f I))
variable [SectionsCoherent I γS hc (smoothLift_x₀ f I) F]
variable [CrisModuleSheaf.IsCrystal F] [CrisModuleSheaf.IsLocallyQuasiCoherent F]

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
  AlgebraicGeometry.Scheme.Modules.DerivedSections.ofComplex A Y
    (SmoothLift.Affine.sheafComplex γA f I γS hc hI hγ hpnil F)

/-- Crystalline derived sections over a p-nilpotent divided-power base are isomorphic
in D(A) to derived sections of the smooth lift's crystal-induced de Rham complex. -/
theorem crystalline_deRham_comparison
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1}
      (liftedRingedSite I γS hc (smoothLift_x₀ f I) p s (smoothLift_p_nilpotent f I hpnil)))]
    [HasSheafify (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian (Sheaf (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A))] :
    IsIsomorphic (crystallineSections f I γS hc hpnil F s)
      (deRhamSections γA f I γS hc hI hγ hpnil F) := sorry

end AlgebraicGeometry.Scheme.Crystalline.SmoothLift
