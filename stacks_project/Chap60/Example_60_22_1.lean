/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap60.Definition_60_9_1
public import stacks_project.Chap60.Example_60_22_1_Rings
public import stacks_project.Chap60.«60_10_0_1_CrystallineSheaf»

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open AlgebraicGeometry.Scheme.Crystalline

namespace Crystalline.SquaredOrigin

/-- Example 60.22.1 (1): `p * τ = 0` in `D`. -/
@[stacks 07LJ]
theorem tau_p_mul {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    (p : data.D) * tau data = 0 := sorry

/-- Example 60.22.1 (2): `d τ = 0` in `Ω_D`. -/
@[stacks 07LJ]
theorem tau_differential {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    crystallineOmegaD_derivation (envelopeBaseMap data) data.γbar p (tau data) = 0 := sorry

/-- Example 60.22.1 (3): `τ ≠ 0` in `D`. -/
@[stacks 07LJ]
theorem tau_ne_zero {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    tau data ≠ 0 := sorry

/-- A ring endomorphism of `D` is a polynomial-Frobenius lift when it raises `x` and `y`
to the `p`th power and is a divided-power morphism for `γ̄`. -/
structure IsPolynomialFrobeniusLift {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (σ : data.D →+* data.D) : Prop where
  map_x : σ data.x = data.x ^ p
  map_y : σ data.y = data.y ^ p
  isDPMorphism : IsDPMorphism data.γbar data.γbar σ

/-- Constructor for a polynomial-Frobenius lift from its three defining conditions. -/
def IsPolynomialFrobeniusLift.of {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (σ : data.D →+* data.D) (map_x : σ data.x = data.x ^ p)
    (map_y : σ data.y = data.y ^ p)
    (isDPMorphism : IsDPMorphism data.γbar data.γbar σ) :
    IsPolynomialFrobeniusLift data σ where
  map_x := map_x
  map_y := map_y
  isDPMorphism := isDPMorphism

/-- Unfolding of a polynomial-Frobenius lift. -/
theorem isPolynomialFrobeniusLift_iff {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (σ : data.D →+* data.D) :
    IsPolynomialFrobeniusLift data σ ↔
      σ data.x = data.x ^ p ∧ σ data.y = data.y ^ p ∧
        IsDPMorphism data.γbar data.γbar σ := sorry

/-- Any polynomial-Frobenius lift of `D` kills `τ`. -/
theorem sigma_tau {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (σ : data.D →+* data.D) (hσ : IsPolynomialFrobeniusLift data σ) :
    σ (tau data) = 0 := sorry

/-- `S = Spec(ℤ_[p])`. -/
abbrev baseScheme (p : ℕ) [Fact p.Prime] : Scheme.{0} :=
  Spec (CommRingCat.of ℤ_[p])

/-- `baseScheme` is the spectrum of `ℤ_[p]`. -/
theorem baseScheme_eq (p : ℕ) [Fact p.Prime] :
    baseScheme p = Spec (CommRingCat.of ℤ_[p]) := sorry

/-- `X = Spec(C)`. -/
abbrev affineScheme (p : ℕ) [Fact p.Prime] : Scheme.{0} :=
  Spec (CommRingCat.of (coordinateRing p))

/-- `affineScheme` is the spectrum of `C`. -/
theorem affineScheme_eq (p : ℕ) [Fact p.Prime] :
    affineScheme p = Spec (CommRingCat.of (coordinateRing p)) := sorry

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

/-- The structure map `Spec(ℤ_[p]) → Spec(ℤ_(p))`. -/
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

/-- The prime `p` is nilpotent on every affine open of `X = Spec(C)`. -/
theorem affine_p_nilpotent (p : ℕ) [Fact p.Prime] (U : (affineScheme p).affineOpens) :
    IsNilpotent (p : Γ(affineScheme p, U)) := sorry

/-- Affine comparison: the ideal sheaf on `Spec(ℤ_[p])` is the quasi-coherent sheaf of
the given ideal of `ℤ_[p]`. -/
def specIdealEqOfIdealTop {p : ℕ} [Fact p.Prime]
    (IA : Ideal ℤ_[p]) (I : (baseScheme p).IdealSheafData) : Prop :=
  I = Scheme.IdealSheafData.ofIdealTop
    (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of ℤ_[p])).hom.hom IA)

/-- Unfolding of `specIdealEqOfIdealTop`. -/
theorem specIdealEqOfIdealTop_iff {p : ℕ} [Fact p.Prime]
    (IA : Ideal ℤ_[p]) (I : (baseScheme p).IdealSheafData) :
    specIdealEqOfIdealTop IA I ↔
      I = Scheme.IdealSheafData.ofIdealTop
        (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of ℤ_[p])).hom.hom IA) := sorry

/-- Global divided powers on `Spec(ℤ_[p])` recover the given divided powers along
`ΓSpecIso`. -/
def specDividedPowersEq {p : ℕ} [Fact p.Prime]
    (IA : Ideal ℤ_[p]) (γA : DividedPowers IA)
    (I : (baseScheme p).IdealSheafData)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers (I.ideal V)) : Prop :=
  IsDPMorphism γA (γS ⟨⊤, isAffineOpen_top (baseScheme p)⟩)
    (Scheme.ΓSpecIso (CommRingCat.of ℤ_[p])).inv.hom

/-- Unfolding of `specDividedPowersEq`. -/
theorem specDividedPowersEq_iff {p : ℕ} [Fact p.Prime]
    (IA : Ideal ℤ_[p]) (γA : DividedPowers IA)
    (I : (baseScheme p).IdealSheafData)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers (I.ideal V)) :
    specDividedPowersEq IA γA I γS ↔
      IsDPMorphism γA (γS ⟨⊤, isAffineOpen_top (baseScheme p)⟩)
        (Scheme.ΓSpecIso (CommRingCat.of ℤ_[p])).inv.hom := sorry

/-- The closed immersion `Spec(C) ⟶ V(I)` is induced by `algebraMap ℤ_[p] C`. -/
def IsCanonicalCrisStructureMap {p : ℕ} [Fact p.Prime]
    (I : (baseScheme p).IdealSheafData)
    (x₀ : affineScheme p ⟶ I.subscheme) : Prop :=
  x₀ ≫ I.subschemeι =
    Spec.map (CommRingCat.ofHom (algebraMap ℤ_[p] (coordinateRing p)))

/-- Unfolding of `IsCanonicalCrisStructureMap`. -/
theorem IsCanonicalCrisStructureMap_iff {p : ℕ} [Fact p.Prime]
    (I : (baseScheme p).IdealSheafData)
    (x₀ : affineScheme p ⟶ I.subscheme) :
    IsCanonicalCrisStructureMap I x₀ ↔
      x₀ ≫ I.subschemeι =
        Spec.map (CommRingCat.ofHom (algebraMap ℤ_[p] (coordinateRing p))) := sorry

/-- The small crystalline topology of `X = Spec(C)` over `S = Spec(ℤ_[p])`. -/
abbrev crisTopology (p : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme) :
    GrothendieckTopology
      (smallCrystallineSite (baseScheme p) (baseIdealSheaf p) γS h_compatible
        (affineScheme p) x₀) :=
  smallCrystallineTopology p (baseScheme p) (baseIdealSheaf p) γS h_compatible
    (baseStructure p) (affineScheme p) x₀ (affine_p_nilpotent p)

/-- `crisTopology` is the small crystalline Zariski topology of this pair. -/
theorem crisTopology_eq (p : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme) :
    crisTopology p γS h_compatible x₀ =
      smallCrystallineTopology p (baseScheme p) (baseIdealSheaf p) γS h_compatible
        (baseStructure p) (affineScheme p) x₀ (affine_p_nilpotent p) := sorry

/-- Global sections of the thickening scheme, as a presheaf of rings on `Cris(X/S)`. -/
def structureRingPresheaf (p : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme) :
    (smallCrystallineSite (baseScheme p) (baseIdealSheaf p) γS h_compatible
      (affineScheme p) x₀)ᵒᵖ ⥤ RingCat.{0} :=
  (smallThickeningFunctor (baseScheme p) (baseIdealSheaf p) γS h_compatible
    (affineScheme p) x₀).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat

/-- `structureRingPresheaf` is global sections of the small thickening functor. -/
theorem structureRingPresheaf_eq (p : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme) :
    structureRingPresheaf p γS h_compatible x₀ =
      (smallThickeningFunctor (baseScheme p) (baseIdealSheaf p) γS h_compatible
        (affineScheme p) x₀).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat := sorry

/-- The crystalline structure sheaf `𝒪_{X/S}` as a sheaf of rings. -/
def structureSheaf (p : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme) :
    Sheaf (crisTopology p γS h_compatible x₀) RingCat.{0} where
  obj := structureRingPresheaf p γS h_compatible x₀
  property := sorry

/-- The underlying presheaf of `structureSheaf` is `structureRingPresheaf`. -/
theorem structureSheaf_obj (p : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme) :
    (structureSheaf p γS h_compatible x₀).obj =
      structureRingPresheaf p γS h_compatible x₀ := sorry

/-- The structure sheaf `𝒪_{X/S}` as the free sheaf of modules of rank one. -/
def structureModuleSheaf (p : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme) :
    SheafOfModules (structureSheaf p γS h_compatible x₀) :=
  SheafOfModules.unit (structureSheaf p γS h_compatible x₀)

/-- `structureModuleSheaf` is the unit sheaf of modules on `𝒪_{X/S}`. -/
theorem structureModuleSheaf_eq (p : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme) :
    structureModuleSheaf p γS h_compatible x₀ =
      SheafOfModules.unit (structureSheaf p γS h_compatible x₀) := sorry

/-- The crystalline structure sheaf viewed as a sheaf of abelian groups. -/
def structureAbelianSheaf (p : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme) :
    Sheaf (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0} :=
  (SheafOfModules.toSheaf _).obj (structureModuleSheaf p γS h_compatible x₀)

/-- `structureAbelianSheaf` forgets the module structure on `𝒪_{X/S}`. -/
theorem structureAbelianSheaf_eq (p : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme) :
    structureAbelianSheaf p γS h_compatible x₀ =
      (SheafOfModules.toSheaf _).obj (structureModuleSheaf p γS h_compatible x₀) := sorry

/-- `H⁰(Cris(X/S), 𝒪_{X/S})`. -/
abbrev cohomology (p : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme)
    [HasSheafify (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0})] :
    AddCommGrpCat.{0} :=
  (Sheaf.functorH (crisTopology p γS h_compatible x₀) 0).obj
    (structureAbelianSheaf p γS h_compatible x₀)

/-- Crystalline `H⁰` is degree-zero sheaf cohomology of `𝒪_{X/S}`. -/
theorem cohomology_eq (p : ℕ) [Fact p.Prime]
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme)
    [HasSheafify (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0})] :
    cohomology p γS h_compatible x₀ =
      (Sheaf.functorH (crisTopology p γS h_compatible x₀) 0).obj
        (structureAbelianSheaf p γS h_compatible x₀) := sorry

/-- Closed elements of `D` for the completed divided-power derivation. -/
def closedForms {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) : AddSubgroup data.D where
  carrier :=
    {a | crystallineOmegaD_derivation (envelopeBaseMap data) data.γbar p a = 0}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in `closedForms` is vanishing of the completed derivation. -/
theorem mem_closedForms {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) (a : data.D) :
    a ∈ closedForms data ↔
      crystallineOmegaD_derivation (envelopeBaseMap data) data.γbar p a = 0 := sorry

/-- Degree-zero de Rham cohomology of `D`, as an abelian group. -/
def deRhamH0 {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) : AddCommGrpCat.{0} :=
  .of (closedForms data : Type)

/-- `deRhamH0` is the abelian group of closed forms. -/
theorem deRhamH0_eq {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    deRhamH0 data = .of (closedForms data : Type) := sorry

/-- Restriction of a polynomial-Frobenius lift to closed forms. -/
def frobeniusOnClosedForms {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (σ : data.D →+* data.D) (hσ : IsPolynomialFrobeniusLift data σ) :
    closedForms data →+ closedForms data :=
  AddMonoidHom.mk'
    (fun z ↦ ⟨σ z.val, sorry⟩)
    sorry

/-- On underlying elements of `D`, `frobeniusOnClosedForms` is `σ`. -/
theorem frobeniusOnClosedForms_apply {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (σ : data.D →+* data.D) (hσ : IsPolynomialFrobeniusLift data σ)
    (z : closedForms data) :
    (frobeniusOnClosedForms data σ hσ z).val = σ z.val := sorry

/-- Proposition 60.21.3 for the structure sheaf: crystalline `H⁰` is the group of
closed forms of `D`. -/
theorem cohomology_iso_deRham {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme)
    (hI : specIdealEqOfIdealTop (padicIdeal p) (baseIdealSheaf p))
    (hγ : specDividedPowersEq (padicIdeal p) (PadicInt.dividedPowers p) (baseIdealSheaf p) γS)
    (hx₀ : IsCanonicalCrisStructureMap (baseIdealSheaf p) x₀)
    [HasSheafify (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0})] :
    IsIsomorphic (cohomology p γS h_compatible x₀) (deRhamH0 data) := sorry

/-- The endomorphism of crystalline `H⁰` induced by a polynomial-Frobenius lift,
as the conjugate of `frobeniusOnClosedForms` along a Proposition 60.21.3
identification `H⁰ ≅ ker(d)`. -/
def frobeniusOnCohomology {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme)
    [HasSheafify (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0})]
    (e : cohomology p γS h_compatible x₀ ≅ deRhamH0 data)
    (σ : data.D →+* data.D) (hσ : IsPolynomialFrobeniusLift data σ) :
    cohomology p γS h_compatible x₀ ⟶ cohomology p γS h_compatible x₀ :=
  e.hom ≫ AddCommGrpCat.ofHom (frobeniusOnClosedForms data σ hσ) ≫ e.inv

/-- `frobeniusOnCohomology` is conjugation of `σ` on closed forms, i.e. the source
identification `F*(τ) = σ(τ)` on `H⁰`. -/
theorem frobeniusOnCohomology_eq {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme)
    [HasSheafify (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0})]
    (e : cohomology p γS h_compatible x₀ ≅ deRhamH0 data)
    (σ : data.D →+* data.D) (hσ : IsPolynomialFrobeniusLift data σ) :
    frobeniusOnCohomology data γS h_compatible x₀ e σ hσ =
      e.hom ≫ AddCommGrpCat.ofHom (frobeniusOnClosedForms data σ hσ) ≫ e.inv := sorry

/-- Example 60.22.1 (4): `H⁰(Cris(X/S), 𝒪_{X/S})` has `p`-torsion. -/
@[stacks 07LJ]
theorem cohomology_has_p_torsion {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme)
    (hI : specIdealEqOfIdealTop (padicIdeal p) (baseIdealSheaf p))
    (hγ : specDividedPowersEq (padicIdeal p) (PadicInt.dividedPowers p) (baseIdealSheaf p) γS)
    (hx₀ : IsCanonicalCrisStructureMap (baseIdealSheaf p) x₀)
    [HasSheafify (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0})] :
    ∃ t : cohomology p γS h_compatible x₀, t ≠ 0 ∧ (p : ℤ) • t = 0 := sorry

/-- Example 60.22.1 (5): a polynomial-Frobenius lift of `x ↦ x^p`, `y ↦ y^p` induces a
non-injective endomorphism of `H⁰(Cris(X/S), 𝒪_{X/S})`; equivalently it kills the class of `τ`. -/
@[stacks 07LJ]
theorem frobeniusPullback_not_injective {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (σ : data.D →+* data.D) (hσ : IsPolynomialFrobeniusLift data σ)
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p ⟶ (baseIdealSheaf p).subscheme)
    (hI : specIdealEqOfIdealTop (padicIdeal p) (baseIdealSheaf p))
    (hγ : specDividedPowersEq (padicIdeal p) (PadicInt.dividedPowers p) (baseIdealSheaf p) γS)
    (hx₀ : IsCanonicalCrisStructureMap (baseIdealSheaf p) x₀)
    [HasSheafify (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p γS h_compatible x₀) AddCommGrpCat.{0})]
    (e : cohomology p γS h_compatible x₀ ≅ deRhamH0 data) :
    ¬ Function.Injective (frobeniusOnCohomology data γS h_compatible x₀ e σ hσ) := sorry

end Crystalline.SquaredOrigin
