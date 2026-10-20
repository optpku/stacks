/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Remark_60_24_9_Base_change_isomorphism_BaseSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_Object
public import stacks_project.Chap60.Remark_60_24_11_Comparison_ModuleDerivedSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients

universe u

namespace CrystallineCompleteSections

variable (p : ℕ) [Fact p.Prime] {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
variable {IA : Ideal A} (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (hI : specIdealEqOfIdealTop IA I)
variable (hpI : IsNilpotent (Ideal.Quotient.mk IA (p : A)))

include hI hpI in
/-- Nilpotence is on the closed fibre, not on the complete base ring. -/
theorem pNilpotentOnClosedFibre :
    ∀ U : (smoothLift f I).affineOpens, IsNilpotent (p : Γ(smoothLift f I, U)) := sorry

variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc (smoothLift f I) (smoothLift_x₀ f I))
variable [SectionsCoherent I γS hc (smoothLift_x₀ f I) F]
variable [CrisModuleSheaf.IsCrystal F]
variable (s : Spec (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))

/-- Actual crystalline derived global sections in D(A), via the base-restricted
derived global sections functor on the small crystalline ringed site. -/
noncomputable def crystallineSections
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1}
      (liftedRingedSite I γS hc (smoothLift_x₀ f I) p s
        (pNilpotentOnClosedFibre p f I hI hpI)))] :
    DerivedCategory (ModuleCat.{u + 1} A) :=
  (CrystallineModuleDerivedSections.baseRestriction A).obj
    ((baseDerivedGlobalSections I γS hc (smoothLift_x₀ f I) p s
      (pNilpotentOnClosedFibre p f I hI hpI)).obj
      (derivedOfCrystal I γS hc (smoothLift_x₀ f I) p s
        (pNilpotentOnClosedFibre p f I hI hpI) F))

end CrystallineCompleteSections
