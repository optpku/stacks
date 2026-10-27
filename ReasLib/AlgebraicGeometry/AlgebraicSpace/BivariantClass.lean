/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.ProperPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections

/-! # Bivariant classes of morphisms of good algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace BivariantClass

variable {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
variable (f : X ⟶ Y) [QuasiSeparated (f ≫ pY)] [LocallyOfFiniteType (f ≫ pY)]

/-- Reindex a Chow group along an equality of its degree indices. -/
def castChowGroup {Z : AlgebraicSpace S} (pZ : Z ⟶ B)
    [QuasiSeparated pZ] [LocallyOfFiniteType pZ] {k l : ℤ} (h : k = l) :
    (Hom.chowGroup pZ) δ k →+ (Hom.chowGroup pZ) δ l :=
  h ▸ AddMonoidHom.id _

/-- Cartesian-square-indexed additive cap maps
`CH_k(Y') →+ CH_{k - p}(X')` for a degree-`p` bivariant class. -/
abbrev CapFamily (p : ℤ) :=
  ∀ {X' Y' : AlgebraicSpace S} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (square : IsPullback i f' f g) (k : ℤ),
    (Hom.chowGroup (g ≫ pY)) δ k →+
      (Hom.chowGroup (i ≫ f ≫ pY)) δ (k - p)

/-- Compatibility of cap maps with proper pushforward along cartesian squares. -/
def CompatibleWithProperPushforward {p : ℤ} (cap : CapFamily δ pY f p) : Prop :=
  ∀ {X' Y' X'' Y'' : AlgebraicSpace S}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (outer : IsPullback i f' f g)
    (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
    [QuasiSeparated (h ≫ g ≫ pY)] [LocallyOfFiniteType (h ≫ g ≫ pY)]
    [QuasiSeparated ((h ≫ g) ≫ pY)] [LocallyOfFiniteType ((h ≫ g) ≫ pY)]
    [QuasiSeparated (j ≫ i ≫ f ≫ pY)] [LocallyOfFiniteType (j ≫ i ≫ f ≫ pY)]
    [QuasiSeparated ((j ≫ i) ≫ f ≫ pY)] [LocallyOfFiniteType ((j ≫ i) ≫ f ≫ pY)]
    (inner : IsPullback j f'' f' h) [Proper h] [Proper j]
    (k : ℤ) (α : (Hom.chowGroup (h ≫ g ≫ pY)) δ k),
    cap i f' g outer k
        (ChowGroup.properPushforward (h ≫ g ≫ pY) (g ≫ pY) δ h rfl k α) =
      ChowGroup.properPushforward (j ≫ i ≫ f ≫ pY) (i ≫ f ≫ pY) δ j rfl (k - p)
        (cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz outer) k α)

/-- Compatibility of cap maps with flat pullback of a fixed relative dimension. -/
def CompatibleWithFlatPullback {p : ℤ} (cap : CapFamily δ pY f p) : Prop :=
  ∀ {X' Y' X'' Y'' : AlgebraicSpace S}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (outer : IsPullback i f' f g)
    (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
    [QuasiSeparated (h ≫ g ≫ pY)] [LocallyOfFiniteType (h ≫ g ≫ pY)]
    [QuasiSeparated ((h ≫ g) ≫ pY)] [LocallyOfFiniteType ((h ≫ g) ≫ pY)]
    [QuasiSeparated (j ≫ i ≫ f ≫ pY)] [LocallyOfFiniteType (j ≫ i ≫ f ≫ pY)]
    [QuasiSeparated ((j ≫ i) ≫ f ≫ pY)] [LocallyOfFiniteType ((j ≫ i) ≫ f ≫ pY)]
    (inner : IsPullback j f'' f' h) (r : ℕ) [Flat h] [RelativeDimension h r]
    [Flat j] [RelativeDimension j r]
    (k : ℤ) (α : (Hom.chowGroup (g ≫ pY)) δ k),
    (castChowGroup δ ((j ≫ i) ≫ f ≫ pY)
        (by omega : k + (r : ℤ) - p = (k - p) + (r : ℤ))).toFun
      (cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz outer) (k + (r : ℤ))
        (ChowGroup.flatPullback (g ≫ pY) (h ≫ g ≫ pY) δ h r rfl k α)) =
      ChowGroup.flatPullback (i ≫ f ≫ pY) ((j ≫ i) ≫ f ≫ pY) δ j r rfl
        (k - p) (cap i f' g outer k α)

/-- Compatibility of cap maps with refined Gysin pullback for a Cartier divisor. -/
def CompatibleWithCartierGysin {p : ℤ} (cap : CapFamily δ pY f p) : Prop :=
  ∀ {X' Y' : AlgebraicSpace S} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (outer : IsPullback i f' f g)
    (L : Y'.Modules) [isInvertibleObject L] (s : L.sections)
    [isInvertibleObject ((Modules.pullback f').obj L)]
    (f'' : (zeroScheme ((Modules.pullback f').obj L)
        (Modules.sectionsPullback f' L s)).X ⟶ (zeroScheme L s).X)
    (inner : IsPullback
      (zeroSchemeι ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s))
      f'' f' (zeroSchemeι L s))
    [QuasiSeparated (zeroSchemeι L s ≫ g ≫ pY)]
    [LocallyOfFiniteType (zeroSchemeι L s ≫ g ≫ pY)]
    [QuasiSeparated ((zeroSchemeι L s ≫ g) ≫ pY)]
    [LocallyOfFiniteType ((zeroSchemeι L s ≫ g) ≫ pY)]
    [QuasiSeparated
      (zeroSchemeι ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s) ≫
        i ≫ f ≫ pY)]
    [LocallyOfFiniteType
      (zeroSchemeι ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s) ≫
        i ≫ f ≫ pY)]
    [QuasiSeparated
      ((zeroSchemeι ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s) ≫
          i) ≫ f ≫ pY)]
    [LocallyOfFiniteType
      ((zeroSchemeι ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s) ≫
          i) ≫ f ≫ pY)]
    (k : ℤ) (α : (Hom.chowGroup (g ≫ pY)) δ (k + 1)),
    cap (zeroSchemeι ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s) ≫ i)
        f'' (zeroSchemeι L s ≫ g) (inner.paste_horiz outer) k
      (ChowGroup.RefinedGysin.gysin (g ≫ pY) δ
        L s k α) =
      ChowGroup.RefinedGysin.gysin (i ≫ f ≫ pY) δ
        ((Modules.pullback f').obj L) (Modules.sectionsPullback f' L s) (k - p)
        ((castChowGroup δ (i ≫ f ≫ pY)
          (by omega : k + 1 - p = (k - p) + 1)).toFun
          (cap i f' g outer (k + 1) α))

end BivariantClass

/-- A degree-`p` bivariant class for a morphism of good algebraic spaces over `B`. -/
structure BivariantClass
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [QuasiSeparated (f ≫ pY)] [LocallyOfFiniteType (f ≫ pY)]
    (p : ℤ) where
  /-- The additive cap action on every cartesian base change. -/
  cap : BivariantClass.CapFamily δ pY f p
  /-- Compatibility with proper pushforward. -/
  map_proper : BivariantClass.CompatibleWithProperPushforward δ pY f cap
  /-- Compatibility with flat pullback of fixed relative dimension. -/
  pullback_flat : BivariantClass.CompatibleWithFlatPullback δ pY f cap
  /-- Compatibility with refined Cartier Gysin pullback. -/
  gysin_cartier : BivariantClass.CompatibleWithCartierGysin δ pY f cap

namespace BivariantClass

variable {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
variable (f : X ⟶ Y) [QuasiSeparated (f ≫ pY)] [LocallyOfFiniteType (f ≫ pY)]

/-- Construct a degree-`p` bivariant class from a cap family and its three
compatibility laws. -/
def ofCap {p : ℤ} (cap : CapFamily δ pY f p)
    (map_proper : CompatibleWithProperPushforward δ pY f cap)
    (pullback_flat : CompatibleWithFlatPullback δ pY f cap)
    (gysin_cartier : CompatibleWithCartierGysin δ pY f cap) :
    BivariantClass δ pY f p where
  cap := cap
  map_proper := map_proper
  pullback_flat := pullback_flat
  gysin_cartier := gysin_cartier

/-- The cap family of `ofCap` is the supplied cap family. -/
theorem ofCap_cap {p : ℤ} (cap : CapFamily δ pY f p)
    (map_proper : CompatibleWithProperPushforward δ pY f cap)
    (pullback_flat : CompatibleWithFlatPullback δ pY f cap)
    (gysin_cartier : CompatibleWithCartierGysin δ pY f cap)
    {X' Y' : AlgebraicSpace S} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [QuasiSeparated (g ≫ pY)] [LocallyOfFiniteType (g ≫ pY)]
    [QuasiSeparated (i ≫ f ≫ pY)] [LocallyOfFiniteType (i ≫ f ≫ pY)]
    (square : IsPullback i f' f g) (k : ℤ) :
    (ofCap δ pY f cap map_proper pullback_flat gysin_cartier).cap i f' g square k =
      cap i f' g square k :=
  rfl

/-- A bivariant class satisfies its proper pushforward, flat pullback, and
Cartier Gysin compatibility laws. -/
theorem spec {p : ℤ} (c : BivariantClass δ pY f p) :
    CompatibleWithProperPushforward δ pY f c.cap ∧
      CompatibleWithFlatPullback δ pY f c.cap ∧
      CompatibleWithCartierGysin δ pY f c.cap :=
  ⟨c.map_proper, c.pullback_flat, c.gysin_cartier⟩

end BivariantClass

end AlgebraicGeometry.AlgebraicSpace
