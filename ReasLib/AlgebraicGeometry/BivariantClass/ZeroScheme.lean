/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Commutativity

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- The canonical comparison from the zero scheme of the pulled-back section to the
source of a displayed cartesian base change. -/
noncomputable def gysinBaseChangeLeftIso
    {S : Scheme.{u}} {X X' Y' : Over S} (L : X.left.Modules)
    [Scheme.Modules.Invertible L] (s : L.sections)
    (i : X' ⟶ Over.mk (Scheme.zeroSchemeι L s ≫ X.hom)) (f' : X' ⟶ Y')
    (g : Y' ⟶ X)
    (square : IsPullback i.left f'.left
      (Over.homMk (Scheme.zeroSchemeι L s) :
        Over.mk (Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X).left g.left) :
    Scheme.zeroScheme ((Scheme.Modules.pullback g.left).obj L)
        (Scheme.Modules.sectionsPullback g.left L s) ≅ X'.left :=
  (Scheme.zeroSchemePullback_isPullback g.left L s
      (Scheme.zeroIdealSheaf_sectionsPullback g.left L s)).isoIsPullback
    _ _ square.flip

/-- The Gysin base-change comparison respects the structure maps to the base scheme. -/
theorem gysinBaseChangeLeftIso_hom_base
    {S : Scheme.{u}} {X X' Y' : Over S} (L : X.left.Modules)
    [Scheme.Modules.Invertible L] (s : L.sections)
    (i : X' ⟶ Over.mk (Scheme.zeroSchemeι L s ≫ X.hom)) (f' : X' ⟶ Y')
    (g : Y' ⟶ X)
    (square : IsPullback i.left f'.left
      (Over.homMk (Scheme.zeroSchemeι L s) :
        Over.mk (Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X).left g.left) :
    (gysinBaseChangeLeftIso L s i f' g square).hom ≫ X'.hom =
      Scheme.zeroSchemeι ((Scheme.Modules.pullback g.left).obj L)
        (Scheme.Modules.sectionsPullback g.left L s) ≫ Y'.hom := sorry

/-- The canonical Gysin base-change comparison as an isomorphism over `S`. -/
noncomputable def gysinBaseChangeIso
    {S : Scheme.{u}} {X X' Y' : Over S} (L : X.left.Modules)
    [Scheme.Modules.Invertible L] (s : L.sections)
    (i : X' ⟶ Over.mk (Scheme.zeroSchemeι L s ≫ X.hom)) (f' : X' ⟶ Y')
    (g : Y' ⟶ X)
    (square : IsPullback i.left f'.left
      (Over.homMk (Scheme.zeroSchemeι L s) :
        Over.mk (Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X).left g.left) :
    Over.mk
        (Scheme.zeroSchemeι ((Scheme.Modules.pullback g.left).obj L)
          (Scheme.Modules.sectionsPullback g.left L s) ≫ Y'.hom) ≅ X' :=
  Over.isoMk (gysinBaseChangeLeftIso L s i f' g square)
    (gysinBaseChangeLeftIso_hom_base L s i f' g square)

/-- The underlying scheme isomorphism of the Gysin base-change comparison. -/
theorem gysinBaseChangeIso_hom_left
    {S : Scheme.{u}} {X X' Y' : Over S} (L : X.left.Modules)
    [Scheme.Modules.Invertible L] (s : L.sections)
    (i : X' ⟶ Over.mk (Scheme.zeroSchemeι L s ≫ X.hom)) (f' : X' ⟶ Y')
    (g : Y' ⟶ X)
    (square : IsPullback i.left f'.left
      (Over.homMk (Scheme.zeroSchemeι L s) :
        Over.mk (Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X).left g.left) :
    (gysinBaseChangeIso L s i f' g square).hom.left =
      (gysinBaseChangeLeftIso L s i f' g square).hom := sorry

/-- The cartesian-square-indexed cap family obtained from zero-scheme Gysin pullback. -/
noncomputable def gysinCap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L] (s : L.sections) :
    CapFamily δ
      (Over.homMk (Scheme.zeroSchemeι L s) :
        Over.mk (Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X) 1 :=
  fun {X' Y'} _ _ i f' g _ square k ↦
    (ChowGroup.map δ
      (Over.mk
        (Scheme.zeroSchemeι ((Scheme.Modules.pullback g.left).obj L)
          (Scheme.Modules.sectionsPullback g.left L s) ≫ Y'.hom))
      X' (gysinBaseChangeIso L s i f' g square).hom (k - 1)).comp
      (ChowGroup.gysin δ Y' ((Scheme.Modules.pullback g.left).obj L)
        (Scheme.Modules.sectionsPullback g.left L s) k)

/-- Each component of the Gysin cap family is Gysin pullback followed by transport across
the canonical base-change isomorphism. -/
theorem gysinCap_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L] (s : L.sections)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ Over.mk (Scheme.zeroSchemeι L s ≫ X.hom)) (f' : X' ⟶ Y')
    (g : Y' ⟶ X) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left
      (Over.homMk (Scheme.zeroSchemeι L s) :
        Over.mk (Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X).left g.left)
    (k : ℤ) :
    gysinCap δ X L s i f' g square k =
      (ChowGroup.map δ
        (Over.mk
          (Scheme.zeroSchemeι ((Scheme.Modules.pullback g.left).obj L)
            (Scheme.Modules.sectionsPullback g.left L s) ≫ Y'.hom))
        X' (gysinBaseChangeIso L s i f' g square).hom (k - 1)).comp
        (ChowGroup.gysin δ Y' ((Scheme.Modules.pullback g.left).obj L)
          (Scheme.Modules.sectionsPullback g.left L s) k) := sorry

/-- The zero-scheme Gysin cap family commutes with proper pushforward. -/
theorem gysinCap_mapProper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L] (s : L.sections) :
    CompatibleWithProperPushforward δ (gysinCap δ X L s) := sorry

/-- The zero-scheme Gysin cap family commutes with flat pullback. -/
theorem gysinCap_pullbackFlat
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L] (s : L.sections) :
    CompatibleWithFlatPullback δ (gysinCap δ X L s) := sorry

/-- The zero-scheme Gysin cap family commutes with Gysin pullback along another
effective Cartier divisor. -/
theorem gysinCap_gysinCartier
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L] (s : L.sections) :
    CompatibleWithCartierGysin δ (gysinCap δ X L s) := sorry

/-- The degree-one bivariant Chow class defined by Gysin pullback along the zero scheme
of a section of an invertible module. -/
noncomputable def gysin
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L] (s : L.sections) :
    BivariantClass δ
      (Over.homMk (Scheme.zeroSchemeι L s) :
        Over.mk (Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X) 1 where
  cap := gysinCap δ X L s
  map_proper := gysinCap_mapProper δ X L s
  pullback_flat := gysinCap_pullbackFlat δ X L s
  gysin_cartier := gysinCap_gysinCartier δ X L s

/-- Evaluation of the Gysin bivariant class is the transported zero-scheme Gysin map. -/
theorem gysin_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L] (s : L.sections)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ Over.mk (Scheme.zeroSchemeι L s ≫ X.hom)) (f' : X' ⟶ Y')
    (g : Y' ⟶ X) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left
      (Over.homMk (Scheme.zeroSchemeι L s) :
        Over.mk (Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X).left g.left)
    (k : ℤ) :
    (gysin δ X L s).cap i f' g square k =
      (ChowGroup.map δ
        (Over.mk
          (Scheme.zeroSchemeι ((Scheme.Modules.pullback g.left).obj L)
            (Scheme.Modules.sectionsPullback g.left L s) ≫ Y'.hom))
        X' (gysinBaseChangeIso L s i f' g square).hom (k - 1)).comp
        (ChowGroup.gysin δ Y' ((Scheme.Modules.pullback g.left).obj L)
          (Scheme.Modules.sectionsPullback g.left L s) k) := sorry

end AlgebraicGeometry.BivariantClass
