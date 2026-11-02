/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.ProperPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.TransferInstance

/-! # Operational Chow classes on algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
  (δ : Points B → ℤ) [IsDimensionFunction δ]
  (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]

namespace OperationalChow

/-- Degree-shifting cap families `CH_k(Y) →+ CH_{k - p}(Y)` on good morphisms
`Y ⟶ X` over `B`. -/
abbrev CapFamily (p : ℤ) :=
  ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
    Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - p)

/-- Cap families expressed as a dependent product over good test morphisms. -/
abbrev CapFamilyPi (p : ℤ) :=
  ∀ (Y : AlgebraicSpace S)
    (t : {g : Y ⟶ X // QuasiSeparated (g ≫ f) ∧ LocallyOfFiniteType (g ≫ f)})
    (k : ℤ),
    @Hom.chowGroup S B Y _ _ (t.val ≫ f) t.property.1 t.property.2 δ _ k →+
      @Hom.chowGroup S B Y _ _ (t.val ≫ f) t.property.1 t.property.2 δ _ (k - p)

/-- Implicitly indexed cap families are equivalent to explicitly indexed cap families. -/
def capFamilyEquiv (p : ℤ) : CapFamily δ f p ≃ CapFamilyPi δ f p where
  toFun c Y t k := @c Y t.val t.property.1 t.property.2 k
  invFun c {Y} g hqs hlft k := c Y ⟨g, hqs, hlft⟩ k
  left_inv _ := rfl
  right_inv _ := rfl

/-- Cap families form an additive commutative group under pointwise operations. -/
instance instAddCommGroupCapFamily (p : ℤ) : AddCommGroup (CapFamily δ f p) :=
  (capFamilyEquiv δ f p).addCommGroup

/-- The zero cap family evaluates to the zero homomorphism. -/
theorem capFamily_zero_apply (p : ℤ) {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (instAddCommGroupCapFamily δ f p).zero g k = 0 := rfl

/-- Addition of cap families evaluates pointwise. -/
theorem capFamily_add_apply {p : ℤ} (c d : CapFamily δ f p)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (instAddCommGroupCapFamily δ f p).add c d g k = c g k + d g k := rfl

/-- Negation of cap families evaluates pointwise. -/
theorem capFamily_neg_apply {p : ℤ} (c : CapFamily δ f p)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (instAddCommGroupCapFamily δ f p).neg c g k = -c g k := rfl

/-- Subtraction of cap families evaluates pointwise. -/
theorem capFamily_sub_apply {p : ℤ} (c d : CapFamily δ f p)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (instAddCommGroupCapFamily δ f p).sub c d g k = c g k - d g k := rfl

/-- Natural multiples of cap families evaluate pointwise. -/
theorem capFamily_nsmul_apply {p : ℤ} (n : ℕ) (c : CapFamily δ f p)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (instAddCommGroupCapFamily δ f p).nsmul n c g k = n • c g k := rfl

/-- Integer multiples of cap families evaluate pointwise. -/
theorem capFamily_zsmul_apply {p : ℤ} (n : ℤ) (c : CapFamily δ f p)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (instAddCommGroupCapFamily δ f p).zsmul n c g k = n • c g k := rfl

/-- Compatibility of identity cap maps with proper pushforward. -/
def CompatibleWithProperPushforward {p : ℤ} (cap : CapFamily δ f p) : Prop :=
  ∀ {Y Y' : AlgebraicSpace S} (g : Y ⟶ X) (h : Y' ⟶ Y)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    [QuasiSeparated (h ≫ g ≫ f)] [LocallyOfFiniteType (h ≫ g ≫ f)]
    [QuasiSeparated ((h ≫ g) ≫ f)] [LocallyOfFiniteType ((h ≫ g) ≫ f)]
    [Proper h]
    (k : ℤ) (α : Hom.chowGroup (h ≫ g ≫ f) δ k),
    cap g k (ChowGroup.properPushforward (h ≫ g ≫ f) (g ≫ f) δ h rfl k α) =
      ChowGroup.properPushforward (h ≫ g ≫ f) (g ≫ f) δ h rfl (k - p)
        (cap (h ≫ g) k α)

/-- Compatibility of identity cap maps with flat pullback of fixed relative
dimension. -/
def CompatibleWithFlatPullback {p : ℤ} (cap : CapFamily δ f p) : Prop :=
  ∀ {Y Y' : AlgebraicSpace S} (g : Y ⟶ X) (h : Y' ⟶ Y)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    [QuasiSeparated (h ≫ g ≫ f)] [LocallyOfFiniteType (h ≫ g ≫ f)]
    [QuasiSeparated ((h ≫ g) ≫ f)] [LocallyOfFiniteType ((h ≫ g) ≫ f)]
    (r : ℕ) [Flat h] [RelativeDimension h r]
    (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k),
    (AddEquiv.cast (M := Hom.chowGroup (h ≫ g ≫ f) δ)
        (show k + (r : ℤ) - p = k - p + (r : ℤ) by omega)).toAddMonoidHom
        (cap (h ≫ g) (k + (r : ℤ))
          (ChowGroup.flatPullback (g ≫ f) (h ≫ g ≫ f) δ h r rfl k α)) =
      ChowGroup.flatPullback (g ≫ f) (h ≫ g ≫ f) δ h r rfl (k - p)
        (cap g k α)

/-- Compatibility of identity cap maps with Gysin pullback along a zero scheme
of a section of an invertible module. -/
def CompatibleWithCartierGysin {p : ℤ} (cap : CapFamily δ f p) : Prop :=
  ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (L : Y.Modules) [isInvertibleObject L] (s : L.sections)
    [QuasiSeparated ((zeroSchemeι L s ≫ g) ≫ f)]
    [LocallyOfFiniteType ((zeroSchemeι L s ≫ g) ≫ f)]
    (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ (k + 1)),
    cap (zeroSchemeι L s ≫ g) k (ChowGroup.RefinedGysin.gysin (g ≫ f) δ L s k α) =
      ChowGroup.RefinedGysin.gysin (g ≫ f) δ L s (k - p)
        ((AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ)
          (show k + 1 - p = k - p + 1 by omega)).toAddMonoidHom (cap g (k + 1) α))

end OperationalChow

/-- A degree-shifting cap family on good test spaces, compatible with proper
pushforward, flat pullback, and refined intersection with zero schemes. -/
structure OperationalChow (p : ℤ) where
  /-- The degree-shifting additive action on every good test space. -/
  cap : OperationalChow.CapFamily δ f p
  /-- Compatibility with canonical proper pushforward. -/
  map_proper : OperationalChow.CompatibleWithProperPushforward δ f cap
  /-- Compatibility with canonical flat pullback of fixed relative dimension. -/
  pullback_flat : OperationalChow.CompatibleWithFlatPullback δ f cap
  /-- Compatibility with refined Gysin for sections of invertible modules. -/
  gysin_cartier : OperationalChow.CompatibleWithCartierGysin δ f cap

namespace OperationalChow

/-- Construct a degree-`p` identity class from a cap family and the three
bivariant laws. -/
def ofCap {p : ℤ} (cap : CapFamily δ f p)
    (map_proper : CompatibleWithProperPushforward δ f cap)
    (pullback_flat : CompatibleWithFlatPullback δ f cap)
    (gysin_cartier : CompatibleWithCartierGysin δ f cap) :
    OperationalChow δ f p where
  cap := cap
  map_proper := map_proper
  pullback_flat := pullback_flat
  gysin_cartier := gysin_cartier

/-- `ofCap` recovers the supplied cap family. -/
theorem ofCap_cap {p : ℤ} (cap : CapFamily δ f p)
    (map_proper : CompatibleWithProperPushforward δ f cap)
    (pullback_flat : CompatibleWithFlatPullback δ f cap)
    (gysin_cartier : CompatibleWithCartierGysin δ f cap)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (ofCap δ f cap map_proper pullback_flat gysin_cartier).cap g k = cap g k :=
  rfl

/-- A degree-`p` identity class is a cap family compatible with proper
pushforward, flat pullback, and Gysin pullback. -/
theorem spec {p : ℤ} (c : OperationalChow δ f p) :
    CompatibleWithProperPushforward δ f c.cap ∧
      CompatibleWithFlatPullback δ f c.cap ∧
      CompatibleWithCartierGysin δ f c.cap :=
  ⟨c.map_proper, c.pullback_flat, c.gysin_cartier⟩

/-- Two identity classes are equal when their cap families agree. -/
theorem cap_ext {p : ℤ} {c d : OperationalChow δ f p}
    (h : ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
      c.cap g k = d.cap g k) :
    c = d := by
  cases c
  cases d
  congr 1
  funext Y g hqs hlft k
  exact h g k

/-- The zero cap family commutes with proper pushforward. -/
theorem zero_proper (p : ℤ) :
    CompatibleWithProperPushforward δ f (p := p) (fun {_} _ _ _ _ ↦ 0) := by
  intro Y Y' g h _ _ _ _ _ _ _ k α
  exact (ChowGroup.properPushforward (h ≫ g ≫ f) (g ≫ f) δ h rfl (k - p)).map_zero.symm

/-- The zero cap family commutes with flat pullback. -/
theorem zero_flat (p : ℤ) :
    CompatibleWithFlatPullback δ f (p := p) (fun {_} _ _ _ _ ↦ 0) := by
  intro Y Y' g h _ _ _ _ _ _ r _ _ k α
  let e := AddEquiv.cast (M := Hom.chowGroup (h ≫ g ≫ f) δ)
    (show k + (r : ℤ) - p = k - p + (r : ℤ) by omega)
  exact e.toAddMonoidHom.map_zero.trans
    (ChowGroup.flatPullback (g ≫ f) (h ≫ g ≫ f) δ h r rfl (k - p)).map_zero.symm

/-- The zero cap family commutes with refined Gysin. -/
theorem zero_gysin (p : ℤ) :
    CompatibleWithCartierGysin δ f (p := p) (fun {_} _ _ _ _ ↦ 0) := by
  intro Y g _ _ L _ s _ _ k α
  let e := AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ)
    (show k + 1 - p = k - p + 1 by omega)
  let G := ChowGroup.RefinedGysin.gysin (g ≫ f) δ L s (k - p)
  exact ((congrArg G e.toAddMonoidHom.map_zero).trans G.map_zero).symm

/-- The operational class whose cap action is pointwise zero. -/
def zero (p : ℤ) : OperationalChow δ f p :=
  ofCap δ f (fun {_} _ _ _ _ ↦ 0)
    (zero_proper δ f p) (zero_flat δ f p) (zero_gysin δ f p)

/-- The cap action of the zero operational class is zero. -/
theorem zero_cap (p : ℤ) {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (zero δ f p).cap g k = 0 := rfl

end OperationalChow

end AlgebraicGeometry.AlgebraicSpace
