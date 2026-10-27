/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.BaseSections
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.AlgebraicGeometry.Crystalline.Affine

@[expose] public section
open AlgebraicGeometry CategoryTheory
universe u
namespace CrystallineModuleDerivedSections
variable (A : Type u) [CommRing A]

/-- The actual map from A to the universe-lifted global functions of
Spec A used by crystalline global sections. -/
noncomputable def baseRingMap : A →+* CrystallineCoefficients.baseRing (Spec (.of A)) :=
  ULift.ringEquiv.symm.toRingHom.comp (Scheme.ΓSpecIso (.of A)).inv.hom

/-- Restrict the actual crystalline base action along ΓSpecIso, retaining
A-linear morphisms in the derived category. -/
noncomputable def baseRestriction :
    DerivedCategory (ModuleCat.{u + 1} (CrystallineCoefficients.baseRing (Spec (.of A)))) ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  (ModuleCat.restrictScalars (baseRingMap A)).mapDerivedCategory


end CrystallineModuleDerivedSections

open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients

namespace AlgebraicGeometry.Scheme.Crystalline

/-- Nilpotence of `p` in `A ⧸ IA` implies local nilpotence of `p` on a scheme
over the closed subscheme of `Spec A` defined by `IA`. -/
theorem p_nilpotent_of_ideal_quotient {p : ℕ} {A : Type u} [CommRing A]
    {IA : Ideal A} (I : (Spec (.of A)).IdealSheafData) {X : Scheme.{u}}
    (x₀ : X ⟶ I.subscheme) (hI : Affine.idealCompatible IA I)
    (hpI : IsNilpotent (Ideal.Quotient.mk IA (p : A))) :
    ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)) := sorry

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
variable (s : Spec (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))

include x₀ in
/-- Nilpotence of `p` on `A` implies local nilpotence of `p` on a scheme over
the closed subscheme `V(I) ⊆ Spec(A)`. -/
theorem p_nilpotent_of_base (hpnil : IsNilpotent (p : A)) :
    ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)) := sorry

variable (hp : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
variable [SectionsCoherent I γS hc x₀ F] [CrisModuleSheaf.IsCrystal F]

/-- Derived global sections `RΓ(Cris(X/S), F)` as an object of `D(A)`, obtained
by restricting the crystalline base action along `ΓSpecIso`. -/
noncomputable def derivedGlobalSections
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1}
      (liftedRingedSite I γS hc x₀ p s hp))] :
    DerivedCategory (ModuleCat.{u + 1} A) :=
  (CrystallineModuleDerivedSections.baseRestriction A).obj
    ((baseDerivedGlobalSections I γS hc x₀ p s hp).obj
      (derivedOfCrystal I γS hc x₀ p s hp F))

/-- `derivedGlobalSections` is restriction of scalars of crystalline derived
global sections of the degree-zero crystal coefficient. -/
theorem derivedGlobalSections_def
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1}
      (liftedRingedSite I γS hc x₀ p s hp))] :
    derivedGlobalSections I γS hc x₀ s hp F =
      (CrystallineModuleDerivedSections.baseRestriction A).obj
        ((baseDerivedGlobalSections I γS hc x₀ p s hp).obj
          (derivedOfCrystal I γS hc x₀ p s hp F)) := sorry


end AlgebraicGeometry.Scheme.Crystalline
