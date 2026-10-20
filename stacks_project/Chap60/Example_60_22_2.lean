/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.GroupTheory.Torsion
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap60.Definition_60_9_1
public import stacks_project.Chap60.Example_60_22_2_DeRham
public import stacks_project.Chap60.Example_60_22_2_Presentation
public import stacks_project.Chap60.Proposition_60_21_1
public import stacks_project.Chap60.«60_10_0_1_CrystallineSheaf»

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Crystalline

namespace Crystalline.AffineSpace

/-- `S = Spec(ℤ_[p])`. -/
abbrev baseScheme (p : ℕ) [Fact p.Prime] : Scheme.{0} :=
  Spec (CommRingCat.of ℤ_[p])

/-- `baseScheme` is affine. -/
theorem baseScheme_isAffine (p : ℕ) [Fact p.Prime] : IsAffine (baseScheme p) := sorry

/-- `X = 𝔸^r_{𝔽_p} = Spec(C)`. -/
abbrev affineScheme (p r : ℕ) [Fact p.Prime] : Scheme.{0} :=
  Spec (CommRingCat.of (coordinateRing p r))

/-- `affineScheme` is affine. -/
theorem affineScheme_isAffine (p r : ℕ) [Fact p.Prime] : IsAffine (affineScheme p r) := sorry

/-- The ideal `(p)` of global functions on `Spec(ℤ_[p])`. -/
def basePrimeIdeal (p : ℕ) [Fact p.Prime] : Ideal Γ(baseScheme p, ⊤) :=
  Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of ℤ_[p])).hom.hom (padicIdeal p)

/-- `basePrimeIdeal` is the comap of `(p)` along `ΓSpecIso`. -/
theorem basePrimeIdeal_eq (p : ℕ) [Fact p.Prime] :
    basePrimeIdeal p =
      Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of ℤ_[p])).hom.hom (padicIdeal p) := sorry

/-- The quasi-coherent ideal sheaf of `(p)` on `Spec(ℤ_[p])`. -/
def baseIdealSheaf (p : ℕ) [Fact p.Prime] : (baseScheme p).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (basePrimeIdeal p)

/-- `baseIdealSheaf` is the ideal sheaf of the global ideal `(p)`. -/
theorem baseIdealSheaf_eq (p : ℕ) [Fact p.Prime] :
    baseIdealSheaf p = Scheme.IdealSheafData.ofIdealTop (basePrimeIdeal p) := sorry

/-- The structure map `Spec(ℤ_[p]) → Spec(ℤ_(p))` induced by `ℤ_(p) → ℤ_[p]`. -/
def baseStructure (p : ℕ) [Fact p.Prime] :
    baseScheme p ⟶ Spec (CommRingCat.of (ULift.{0} (Int.LocalizationAtPrime p))) :=
  let e : ULift.{0} (Int.LocalizationAtPrime p) ≃+* Int.LocalizationAtPrime p :=
    ULift.ringEquiv
  Spec.map (CommRingCat.ofHom ((fromLocalization p).comp e.toRingHom))

/-- `baseStructure` is `Spec` of `ℤ_(p) → ℤ_[p]`. -/
theorem baseStructure_eq (p : ℕ) [Fact p.Prime] :
    baseStructure p =
      let e : ULift.{0} (Int.LocalizationAtPrime p) ≃+* Int.LocalizationAtPrime p :=
        ULift.ringEquiv
      Spec.map (CommRingCat.ofHom ((fromLocalization p).comp e.toRingHom)) := sorry

/-- The prime `p` is nilpotent on every affine open of `𝔸^r_{𝔽_p}`. -/
theorem affine_p_nilpotent (p r : ℕ) [Fact p.Prime] (U : (affineScheme p r).affineOpens) :
    IsNilpotent (p : Γ(affineScheme p r, U)) := sorry

/-- The small crystalline topology of `𝔸^r_{𝔽_p}` over `Spec(ℤ_[p])`. -/
def crisTopology (p r : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p r ⟶ (baseIdealSheaf p).subscheme) :
    GrothendieckTopology
      (smallCrystallineSite (baseScheme p) (baseIdealSheaf p) γS h_compatible
        (affineScheme p r) x₀) :=
  smallCrystallineTopology p (baseScheme p) (baseIdealSheaf p) γS h_compatible
    (baseStructure p) (affineScheme p r) x₀ (affine_p_nilpotent p r)

/-- `crisTopology` is the small crystalline Zariski topology of this affine pair. -/
theorem crisTopology_eq (p r : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p r ⟶ (baseIdealSheaf p).subscheme) :
    crisTopology p r γS h_compatible x₀ =
      smallCrystallineTopology p (baseScheme p) (baseIdealSheaf p) γS h_compatible
        (baseStructure p) (affineScheme p r) x₀ (affine_p_nilpotent p r) := sorry

section Cohomology

variable {p : ℕ} [Fact p.Prime] (r : ℕ)
variable (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
variable (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
  (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
    ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
variable (x₀ : affineScheme p r ⟶ (baseIdealSheaf p).subscheme)
variable [HasSheafify (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0}]
variable [HasExt.{0} (Sheaf (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0})]

/-- Global sections of the thickening scheme, as a presheaf of rings on `Cris(X/S)`. -/
def structureRingPresheaf :
    (smallCrystallineSite (baseScheme p) (baseIdealSheaf p) γS h_compatible
      (affineScheme p r) x₀)ᵒᵖ ⥤ RingCat.{0} :=
  (smallThickeningFunctor (baseScheme p) (baseIdealSheaf p) γS h_compatible
    (affineScheme p r) x₀).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat

/-- `structureRingPresheaf` is global sections along `smallThickeningFunctor`. -/
theorem structureRingPresheaf_eq :
    structureRingPresheaf r γS h_compatible x₀ =
      (smallThickeningFunctor (baseScheme p) (baseIdealSheaf p) γS h_compatible
        (affineScheme p r) x₀).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat := sorry

/-- The structure sheaf `𝒪_{X/S}` on the small crystalline site. -/
def structureRingSheaf :
    Sheaf (crisTopology p r γS h_compatible x₀) RingCat.{0} where
  obj := structureRingPresheaf r γS h_compatible x₀
  property := sorry

/-- `structureRingSheaf` is the global-sections presheaf of the thickening functor. -/
theorem structureRingSheaf_obj :
    (structureRingSheaf r γS h_compatible x₀).obj =
      structureRingPresheaf r γS h_compatible x₀ := sorry

/-- The structure sheaf `𝒪_{X/S}` as the free sheaf of modules of rank one. -/
def structureModuleSheaf :
    SheafOfModules (structureRingSheaf r γS h_compatible x₀) :=
  SheafOfModules.unit (structureRingSheaf r γS h_compatible x₀)

/-- `structureModuleSheaf` is the unit sheaf of modules on `𝒪_{X/S}`. -/
theorem structureModuleSheaf_eq :
    structureModuleSheaf r γS h_compatible x₀ =
      SheafOfModules.unit (structureRingSheaf r γS h_compatible x₀) := sorry

/-- The crystalline structure sheaf viewed as a sheaf of abelian groups. -/
def structureAbelianSheaf :
    Sheaf (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0} :=
  (SheafOfModules.toSheaf _).obj (structureModuleSheaf r γS h_compatible x₀)

/-- `structureAbelianSheaf` forgets the module structure on `𝒪_{X/S}`. -/
theorem structureAbelianSheaf_eq :
    structureAbelianSheaf r γS h_compatible x₀ =
      (SheafOfModules.toSheaf _).obj (structureModuleSheaf r γS h_compatible x₀) := sorry

/-- `H^i(Cris(X/S), 𝒪_{X/S})` for `X = 𝔸^r_{𝔽_p}` and `S = Spec(ℤ_[p])`. -/
abbrev cohomology (i : ℕ) : AddCommGrpCat.{0} :=
  (Sheaf.functorH (crisTopology p r γS h_compatible x₀) i).obj
    (structureAbelianSheaf r γS h_compatible x₀)

/-- Crystalline cohomology is sheaf cohomology of the crystalline structure sheaf. -/
theorem cohomology_eq (i : ℕ) :
    cohomology r γS h_compatible x₀ i =
      (Sheaf.functorH (crisTopology p r γS h_compatible x₀) i).obj
        (structureAbelianSheaf r γS h_compatible x₀) := sorry

/-- Example 60.22.2 (1): `RΓ(Cris(X/S), 𝒪_{X/S})` is represented by the completed de Rham
complex of `P = ℤ_[p][x₁,…,x_r]`. -/
@[stacks 07LK]
theorem representedByCompletedDeRham
    (hI : specIdealEqOfIdealTop (padicIdeal p) (baseIdealSheaf p))
    (hγ : specDividedPowersEq (padicIdeal p) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : IsCanonicalCrisStructureMap (baseIdealSheaf p) x₀) (i : ℕ) :
    IsIsomorphic (cohomology r γS h_compatible x₀ i)
      ((forget₂ (ModuleCat.{0} ℤ_[p]) AddCommGrpCat.{0}).obj
        ((completedDeRham p r).homology i)) := sorry

/-- Example 60.22.2 (2): for `r > 0`, crystalline cohomology of `𝒪_{X/S}` vanishes
outside degrees `0, …, r`. -/
@[stacks 07LK]
theorem vanishesAbove
    (hI : specIdealEqOfIdealTop (padicIdeal p) (baseIdealSheaf p))
    (hγ : specDividedPowersEq (padicIdeal p) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : IsCanonicalCrisStructureMap (baseIdealSheaf p) x₀)
    (hr : 0 < r) (i : ℕ) (hi : r < i) :
    Limits.IsZero (cohomology r γS h_compatible x₀ i) := sorry

/-- Example 60.22.2 (3): for `r > 0`, `H^0(Cris(X/S), 𝒪_{X/S})` is `ℤ_[p]`. -/
@[stacks 07LK]
theorem cohomologyZero
    (hI : specIdealEqOfIdealTop (padicIdeal p) (baseIdealSheaf p))
    (hγ : specDividedPowersEq (padicIdeal p) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : IsCanonicalCrisStructureMap (baseIdealSheaf p) x₀) (hr : 0 < r) :
    IsIsomorphic (cohomology r γS h_compatible x₀ 0) (AddCommGrpCat.of ℤ_[p]) := sorry

/-- Example 60.22.2 (4): for `r > 0`, `H^r(Cris(X/S), 𝒪_{X/S})` is infinite. -/
@[stacks 07LK]
theorem topInfinite
    (hI : specIdealEqOfIdealTop (padicIdeal p) (baseIdealSheaf p))
    (hγ : specDividedPowersEq (padicIdeal p) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : IsCanonicalCrisStructureMap (baseIdealSheaf p) x₀) (hr : 0 < r) :
    Infinite (cohomology r γS h_compatible x₀ r : Type) := sorry

/-- Example 60.22.2 (5): for `r > 0`, `H^r(Cris(X/S), 𝒪_{X/S})` is not a torsion
abelian group. -/
@[stacks 07LK]
theorem topNotTorsion
    (hI : specIdealEqOfIdealTop (padicIdeal p) (baseIdealSheaf p))
    (hγ : specDividedPowersEq (padicIdeal p) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : IsCanonicalCrisStructureMap (baseIdealSheaf p) x₀) (hr : 0 < r) :
    ¬ AddMonoid.IsTorsion (cohomology r γS h_compatible x₀ r : Type) := sorry

/-- Example 60.22.2 (6): for `r > 0`, `H^r(Cris(X/S), 𝒪_{X/S})` is not separated for
the p-adic topology. -/
@[stacks 07LK]
theorem topNotHausdorff
    (hI : specIdealEqOfIdealTop (padicIdeal p) (baseIdealSheaf p))
    (hγ : specDividedPowersEq (padicIdeal p) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : IsCanonicalCrisStructureMap (baseIdealSheaf p) x₀) (hr : 0 < r) :
    ¬ IsHausdorff (Ideal.span ({(p : ℤ)} : Set ℤ))
        (cohomology r γS h_compatible x₀ r : Type) := sorry

/-- The representing top homology module is not Hausdorff for the `(p)`-adic topology. -/
theorem homology_top_not_hausdorff (hr : 0 < r) :
    ¬ IsHausdorff (padicIdeal p) ((completedDeRham p r).homology r : Type) := sorry

end Cohomology

/-- Example 60.22.2 (7): the class of `η` generates an injective copy of `ℚ_[p]` in the
cokernel of the completed line differential. -/
@[stacks 07LK]
theorem existsInjectivePadicRat (p : ℕ) [Fact p.Prime] :
    ∃ f : ℚ_[p] →+ lineCoker p, Function.Injective f := sorry

end Crystalline.AffineSpace
