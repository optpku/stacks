/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Remark_60_24_9_Base_change_isomorphism_BaseSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_ModuleDerivedSections
public import stacks_project.Chap60.Definition_60_11_3_Crystal
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
import Mathlib.Tactic.CrossRefAttribute

public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.Perfect
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients SheafOfModules

universe u

/- Remark 60.24.12 (Perfectness): crystalline cohomology of a finite locally free
quasi-coherent crystal on a proper smooth scheme over the closed fibre of a
divided-power ring with nilpotent `p` is perfect over the base ring. -/
@[stacks 07MX] #check
  (AlgebraicGeometry.Scheme.Crystalline.derivedGlobalSections_isPerfect :
    ∀ {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    {IA : Ideal A} (γA : DividedPowers IA)
    (I : (Spec (.of A)).IdealSheafData)
    (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
    (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
      (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
        ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
    {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
    (s : Spec (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (F : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
    [SectionsCoherent I γS hc x₀ F] [CrisModuleSheaf.IsCrystal F]
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
      (liftedRingedSite I γS hc x₀ p s (p_nilpotent_of_base I x₀ hpnil)))],
    (derivedGlobalSections I γS hc x₀ s (p_nilpotent_of_base I x₀ hpnil) F).IsPerfect)
