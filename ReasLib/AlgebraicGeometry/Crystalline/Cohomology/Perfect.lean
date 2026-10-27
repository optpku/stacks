/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.AffineBase
public import ReasLib.AlgebraicGeometry.Crystalline.Affine
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Crystal
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients SheafOfModules

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

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

variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
variable [SectionsCoherent I γS hc x₀ F] [CrisModuleSheaf.IsCrystal F]

/-- Over a divided-power ring in which the prime `p` is nilpotent, the crystalline
cohomology of a finite locally free quasi-coherent crystal on a proper smooth scheme
over the closed fibre is a perfect object of `D(A)`. No Noetherianity or nilpotence
of the divided-power ideal is required. -/
theorem derivedGlobalSections_isPerfect
    (hI : Affine.idealCompatible IA I) (hγ : Affine.dividedPowersCompatible IA γA I γS)
    (hpnil : IsNilpotent (p : A))
    [IsProper x₀] [Smooth x₀]
    [HasWeakSheafify (smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀
      (p_nilpotent_of_base I x₀ hpnil)) AddCommGrpCat.{u}]
    [(smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀
      (p_nilpotent_of_base I x₀ hpnil)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite (Spec (.of A)) I γS hc X x₀,
      HasWeakSheafify ((smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀
        (p_nilpotent_of_base I x₀ hpnil)).over U) AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite (Spec (.of A)) I γS hc X x₀,
      ((smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀
        (p_nilpotent_of_base I x₀ hpnil)).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [IsCrystalInFiniteLocallyFreeModules
      (ofCrystal I γS hc x₀ F p s (p_nilpotent_of_base I x₀ hpnil))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1}
      (liftedRingedSite I γS hc x₀ p s (p_nilpotent_of_base I x₀ hpnil)))] :
    (derivedGlobalSections I γS hc x₀ s (p_nilpotent_of_base I x₀ hpnil) F).IsPerfect := sorry

/-- Over a `p`-adically complete divided-power ring `A` with `p` nilpotent in
`A ⧸ IA`, crystalline cohomology of a finite locally free quasi-coherent crystal
on a proper smooth scheme over the closed fibre is a perfect object of `D(A)`. -/
theorem derivedGlobalSections_isPerfect_of_isAdicComplete
    (hI : Affine.idealCompatible IA I) (hγ : Affine.dividedPowersCompatible IA γA I γS)
    (hpI : IsNilpotent (Ideal.Quotient.mk IA (p : A)))
    [IsAdicComplete (Ideal.span {(p : A)}) A]
    [IsProper x₀] [Smooth x₀]
    [HasWeakSheafify (smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀
      (p_nilpotent_of_ideal_quotient I x₀ hI hpI)) AddCommGrpCat.{u}]
    [(smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀
      (p_nilpotent_of_ideal_quotient I x₀ hI hpI)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite (Spec (.of A)) I γS hc X x₀,
      HasWeakSheafify ((smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀
        (p_nilpotent_of_ideal_quotient I x₀ hI hpI)).over U) AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite (Spec (.of A)) I γS hc X x₀,
      ((smallCrystallineTopology p (Spec (.of A)) I γS hc s X x₀
        (p_nilpotent_of_ideal_quotient I x₀ hI hpI)).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    [IsCrystalInFiniteLocallyFreeModules
      (ofCrystal I γS hc x₀ F p s (p_nilpotent_of_ideal_quotient I x₀ hI hpI))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1}
      (liftedRingedSite I γS hc x₀ p s (p_nilpotent_of_ideal_quotient I x₀ hI hpI)))] :
    (derivedGlobalSections I γS hc x₀ s
      (p_nilpotent_of_ideal_quotient I x₀ hI hpI) F).IsPerfect := sorry

end AlgebraicGeometry.Scheme.Crystalline
