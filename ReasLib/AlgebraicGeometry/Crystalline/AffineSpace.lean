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
public import ReasLib.AlgebraicGeometry.Crystalline.Affine
public import ReasLib.AlgebraicGeometry.Crystalline.Thickening
public import ReasLib.RingTheory.Kaehler.DeRham.PadicPolynomial
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Crystalline
open PadicPolynomial

namespace Crystalline.AffineSpace

/-- `S = Spec(ℤ_[p])`. -/
abbrev baseScheme (p : ℕ) [Fact p.Prime] : Scheme.{0} :=
  Spec (CommRingCat.of ℤ_[p])


/-- `X = 𝔸^r_{𝔽_p} = Spec(C)`. -/
abbrev affineScheme (p r : ℕ) [Fact p.Prime] : Scheme.{0} :=
  Spec (CommRingCat.of (coordinateRing p r))


/-- The ideal `(p)` of global functions on `Spec(ℤ_[p])`. -/
def basePrimeIdeal (p : ℕ) [Fact p.Prime] : Ideal Γ(baseScheme p, ⊤) :=
  Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of ℤ_[p])).hom.hom (Ideal.span {(p : ℤ_[p])})


/-- The quasi-coherent ideal sheaf of `(p)` on `Spec(ℤ_[p])`. -/
def baseIdealSheaf (p : ℕ) [Fact p.Prime] : (baseScheme p).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (basePrimeIdeal p)


/-- The structure map `Spec(ℤ_[p]) → Spec(ℤ_(p))` induced by `ℤ_(p) → ℤ_[p]`. -/
def baseStructure (p : ℕ) [Fact p.Prime] :
    baseScheme p ⟶ Spec (CommRingCat.of (ULift.{0} (Int.LocalizationAtPrime p))) :=
  let e : ULift.{0} (Int.LocalizationAtPrime p) ≃+* Int.LocalizationAtPrime p :=
    ULift.ringEquiv
  Spec.map (CommRingCat.ofHom ((PadicInt.fromLocalization p).comp e.toRingHom))


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


/-- The presheaf of functions on crystalline thickenings satisfies the sheaf condition. -/
theorem structureRingPresheaf_isSheaf :
    Presheaf.IsSheaf (crisTopology p r γS h_compatible x₀)
      (structureRingPresheaf r γS h_compatible x₀) := sorry

/-- The structure sheaf `𝒪_{X/S}` on the small crystalline site. -/
def structureRingSheaf :
    Sheaf (crisTopology p r γS h_compatible x₀) RingCat.{0} where
  obj := structureRingPresheaf r γS h_compatible x₀
  property := structureRingPresheaf_isSheaf r γS h_compatible x₀

/-- `structureRingSheaf` is the global-sections presheaf of the thickening functor. -/
theorem structureRingSheaf_obj :
    (structureRingSheaf r γS h_compatible x₀).obj =
      structureRingPresheaf r γS h_compatible x₀ := rfl

/-- The structure sheaf `𝒪_{X/S}` as the free sheaf of modules of rank one. -/
def structureModuleSheaf :
    SheafOfModules (structureRingSheaf r γS h_compatible x₀) :=
  SheafOfModules.unit (structureRingSheaf r γS h_compatible x₀)


/-- The crystalline structure sheaf viewed as a sheaf of abelian groups. -/
def structureAbelianSheaf :
    Sheaf (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0} :=
  (SheafOfModules.toSheaf _).obj (structureModuleSheaf r γS h_compatible x₀)


/-- `H^i(Cris(X/S), 𝒪_{X/S})` for `X = 𝔸^r_{𝔽_p}` and `S = Spec(ℤ_[p])`. -/
abbrev cohomology (i : ℕ) : AddCommGrpCat.{0} :=
  (Sheaf.functorH (crisTopology p r γS h_compatible x₀) i).obj
    (structureAbelianSheaf r γS h_compatible x₀)


/-- Derived global sections of the additive crystalline structure sheaf in degree zero. -/
def derivedGlobalSections
    [HasGlobalSectionsFunctor (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0}]
    [IsGrothendieckAbelian (Sheaf (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0})] :
    DerivedCategory AddCommGrpCat.{0} :=
  (CategoryTheory.siteAbelianGlobalSectionsDerived (crisTopology p r γS h_compatible x₀)).obj
    ((DerivedCategory.singleFunctor _ 0).obj (structureAbelianSheaf r γS h_compatible x₀))

/-- Derived crystalline global sections are represented by the completed polynomial de Rham
complex, extended by zero to negative degrees. -/
theorem representedByCompletedDeRham
    [HasGlobalSectionsFunctor (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0}]
    [IsGrothendieckAbelian (Sheaf (crisTopology p r γS h_compatible x₀) AddCommGrpCat.{0})]
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀) :
    IsIsomorphic (derivedGlobalSections r γS h_compatible x₀)
      (DerivedCategory.Q.obj
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{0}).obj
          (((forget₂ (ModuleCat.{0} ℤ_[p]) AddCommGrpCat.{0}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (completedDeRham p r)))) := sorry

/-- Crystalline cohomology is isomorphic degreewise to the homology of the completed
polynomial de Rham complex. -/
theorem cohomologyIsoCompletedDeRham
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀) (i : ℕ) :
    IsIsomorphic (cohomology r γS h_compatible x₀ i)
      ((forget₂ (ModuleCat.{0} ℤ_[p]) AddCommGrpCat.{0}).obj
        ((completedDeRham p r).homology i)) := sorry

/-- For positive-dimensional affine space, crystalline cohomology of `𝒪_{X/S}` vanishes
outside degrees `0, …, r`. -/
theorem vanishesAbove
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀)
    (hr : 0 < r) (i : ℕ) (hi : r < i) :
    Limits.IsZero (cohomology r γS h_compatible x₀ i) := sorry

/-- For positive-dimensional affine space, `H^0(Cris(X/S), 𝒪_{X/S})` is `ℤ_[p]`. -/
theorem cohomologyZero
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀) (hr : 0 < r) :
    IsIsomorphic (cohomology r γS h_compatible x₀ 0) (AddCommGrpCat.of ℤ_[p]) := sorry

/-- For positive-dimensional affine space, `H^r(Cris(X/S), 𝒪_{X/S})` is infinite. -/
theorem topInfinite
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀) (hr : 0 < r) :
    Infinite (cohomology r γS h_compatible x₀ r : Type) := sorry

/-- For positive-dimensional affine space, `H^r(Cris(X/S), 𝒪_{X/S})` is not a torsion
abelian group. -/
theorem topNotTorsion
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀) (hr : 0 < r) :
    ¬ AddMonoid.IsTorsion (cohomology r γS h_compatible x₀ r : Type) := sorry

/-- For positive-dimensional affine space, `H^r(Cris(X/S), 𝒪_{X/S})` is not separated for
the p-adic topology. -/
theorem topNotHausdorff
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀) (hr : 0 < r) :
    ¬ IsHausdorff (Ideal.span ({(p : ℤ)} : Set ℤ))
        (cohomology r γS h_compatible x₀ r : Type) := sorry


/-- Crystalline cohomology of the affine line in degree one contains an additive copy
of the field of `p`-adic numbers. -/
theorem existsInjectivePadicRatCohomology
    (γS : ∀ V : (baseScheme p).affineOpens, DividedPowers ((baseIdealSheaf p).ideal V))
    (h_compatible : ∀ (V : (baseScheme p).affineOpens) (f : Γ(baseScheme p, V)),
      (γS V).IsDPMorphism (γS ((baseScheme p).affineBasicOpen f))
        ((baseScheme p).presheaf.map (homOfLE ((baseScheme p).basicOpen_le f)).op).hom)
    (x₀ : affineScheme p 1 ⟶ (baseIdealSheaf p).subscheme)
    [HasSheafify (crisTopology p 1 γS h_compatible x₀) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (crisTopology p 1 γS h_compatible x₀) AddCommGrpCat.{0})]
    (hI : Affine.idealCompatible (Ideal.span {(p : ℤ_[p])}) (baseIdealSheaf p))
    (hγ : Affine.dividedPowersCompatible (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)
      (baseIdealSheaf p) γS)
    (hx₀ : Affine.structureMapCompatible (baseIdealSheaf p) x₀) :
    ∃ f : ℚ_[p] →+ (cohomology 1 γS h_compatible x₀ 1 : Type),
      Function.Injective f := sorry

end Cohomology


end Crystalline.AffineSpace
