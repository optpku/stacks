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

include x₀ in
/-- Nilpotence of `p` on `A` implies local nilpotence of `p` on a scheme over
the closed subscheme `V(I) ⊆ Spec(A)`. -/
theorem p_nilpotent_of_base (hpnil : IsNilpotent (p : A)) :
    ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)) :=
  sorry

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
          (derivedOfCrystal I γS hc x₀ p s hp F)) :=
  sorry

/-- Remark 60.24.12 (Perfectness): if `p` is prime, `(A, I, γ)` is a
divided-power ring with `p` nilpotent in `A`, `S = Spec(A)`, `S₀ = V(I)`,
`X` is proper and smooth over `S₀`, and `F` is a crystal in finite locally
free quasi-coherent `𝒪_{X/S}`-modules, then `RΓ(Cris(X/S), F)` is a perfect
object of `D(A)`. -/
@[stacks 07MX]
theorem derivedGlobalSections_isPerfect
    (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
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
    (derivedGlobalSections I γS hc x₀ s (p_nilpotent_of_base I x₀ hpnil) F).IsPerfect :=
  sorry

end AlgebraicGeometry.Scheme.Crystalline

