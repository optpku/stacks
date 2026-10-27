/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Crystalline.Completed.SmoothLiftCoefficients
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.AffineBase
public import ReasLib.AlgebraicGeometry.Crystalline.PPower
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RingTheory.Noetherian.Defs


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.Complete

variable (p : ℕ) [Fact p.Prime] {A : Type u} [CommRing A]
variable [IsAdicComplete (Ideal.span {(p : A)}) A]
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
variable {IA : Ideal A} (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (hI : Affine.idealCompatible IA I)
variable (hpI : IsNilpotent (Ideal.Quotient.mk IA (p : A)))

include hI hpI in
/-- Nilpotence is on the closed fibre, not on the complete base ring. -/
theorem pNilpotentOnClosedFibre :
    ∀ U : (smoothLift f I).affineOpens, IsNilpotent (p : Γ(smoothLift f I, U)) := sorry

variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc (smoothLift f I) (smoothLift_x₀ f I))
variable [CrisModuleSheaf.IsCrystal F]

/-- Actual crystalline derived global sections in D(A), via the base-restricted
derived global sections functor on the small crystalline ringed site. -/
noncomputable def crystallineSections
 :
    DerivedCategory (ModuleCat.{u + 1} A) :=
  (CrystallineModuleDerivedSections.baseRestriction A).obj
    ((baseDerivedGlobalSections I γS hc (smoothLift_x₀ f I) p (PPower.baseMap A p)
      (pNilpotentOnClosedFibre p f I hI hpI)).obj
      (derivedOfCrystal I γS hc (smoothLift_x₀ f I) p (PPower.baseMap A p)
        (pNilpotentOnClosedFibre p f I hI hpI) F))

end AlgebraicGeometry.Scheme.Crystalline.Complete

open AlgebraicGeometry.Scheme.Modules.DeRham
namespace AlgebraicGeometry.Scheme.Crystalline.Complete

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [hNoetherian : IsNoetherianRing A]
variable [hComplete : IsAdicComplete (Ideal.span {(p : A)}) A]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [hSmooth : Smooth f] [hProper : IsProper f]
variable (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (hI : Affine.idealCompatible IA I) (hγ : Affine.dividedPowersCompatible IA γA I γS)
variable (hpI : IsNilpotent (Ideal.Quotient.mk IA (p : A)))
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc (smoothLift f I) (smoothLift_x₀ f I))
variable [CrisModuleSheaf.IsCrystal F] [hqc : CrisModuleSheaf.IsLocallyQuasiCoherent F]

variable (hft : ∀ Aobj, (F.obj Aobj).IsFiniteType)

include hft hNoetherian hComplete hSmooth hProper hqc in
/-- A coherent algebraization with horizontal, transition-compatible crystalline reductions
has crystalline cohomology isomorphic to its de Rham cohomology. -/
theorem crystalline_deRham_comparison (FY : Y.Modules) (hcoh : FY.IsCoherent)
    (nabla : asBaseSheaf f FY ⟶ asBaseSheaf f (oneFormTensor f FY))
    (hconn : IsConnection f FY nabla) (hnabla : IsIntegrable f FY hcoh nabla hconn)
    (hred : ReductionSystem γA f I γS hc hI hγ hpI F FY nabla) :
    IsIsomorphic (crystallineSections p f I γS hc hI hpI F)
      (deRhamSections f FY hcoh nabla hconn hnabla) := sorry

include hft hNoetherian hComplete hSmooth hProper hqc in
/-- A finite type quasi-coherent crystal on the closed fibre of a proper smooth scheme over
a Noetherian p-adically complete divided-power ring algebraizes to a coherent module with
integrable connection and compatible crystalline reductions. Its crystalline derived global
sections are isomorphic to the de Rham derived global sections of that same algebraization. -/
theorem exists_algebraization_comparison :
    ∃ (FY : Y.Modules) (hcoh : FY.IsCoherent)
      (nabla : asBaseSheaf f FY ⟶ asBaseSheaf f (oneFormTensor f FY))
      (hconn : IsConnection f FY nabla) (hnabla : IsIntegrable f FY hcoh nabla hconn)
      (hred : ReductionSystem γA f I γS hc hI hγ hpI F FY nabla),
      IsIsomorphic (crystallineSections p f I γS hc hI hpI F)
        (deRhamSections f FY hcoh nabla hconn hnabla) := sorry

end AlgebraicGeometry.Scheme.Crystalline.Complete
