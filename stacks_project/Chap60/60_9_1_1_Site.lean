/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Basic
public import stacks_project.Chap60.«60_8_1_1»
public import ReasLib.RingTheory.Localization.AtPrime.Int

@[expose] public section

open AlgebraicGeometry CategoryTheory MorphismProperty

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Crystalline

/- The small crystalline site is the full subcategory of `RelativeCRIS` on crystalline
objects whose source over `X` is an open immersion. -/
/-- The object property selecting crystalline objects with open source over `X`. -/
abbrev smallCrystallineProperty
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :
    ObjectProperty (RelativeCRIS S I γ h_compatible X x₀) :=
  fun T ↦ IsOpenImmersion T.1.source.hom

/-- The full small crystalline site `Cris(X/S)` of crystalline objects with open source. -/
abbrev smallCrystallineSite
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :=
  (smallCrystallineProperty S I γ h_compatible X x₀).FullSubcategory

/-- The open source in `X.smallZariskiSite` underlying a small crystalline object. -/
def smallCrystallineSource
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) : X.smallZariskiSite :=
  let c := T.obj.1
  let U := c.source
  Over.mk ⊤ U.hom T.property

/-- The induced morphism of open sources associated to a small crystalline morphism. -/
def smallCrystallineSourceMap
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    {T U : smallCrystallineSite S I γ h_compatible X x₀}
    (f : T ⟶ U) : smallCrystallineSource S I γ h_compatible X x₀ T ⟶
      smallCrystallineSource S I γ h_compatible X x₀ U :=
  let φ := f.hom.source
  Over.Hom.mk φ trivial

end Crystalline
end Scheme
end AlgebraicGeometry
