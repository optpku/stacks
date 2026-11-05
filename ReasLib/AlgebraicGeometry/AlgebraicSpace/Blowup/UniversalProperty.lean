/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.ExceptionalDivisor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Pullback
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Universal property of blowups of algebraic spaces

The blowup along a closed subspace is final among spaces over the ambient space
on which the inverse image of the center is an effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Blowup

/-- The full subcategory of spaces over `X` whose inverse image of the closed
subspace `Z` is an effective Cartier divisor. -/
abbrev effectiveCartierPullbackOverCategory {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) :=
  ObjectProperty.FullSubcategory fun Y : Over X ↦
    IsEffectiveCartierDivisor (Z.inverseImageSubspace Y.hom).ι

namespace effectiveCartierPullbackOverCategory

/-- The explicit inverse-image subspace and the categorical pullback define the
same effective-Cartier condition. -/
theorem inverseImage_isEffectiveCartier_iff_pullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (Z : ClosedSubspace X) (g : Y ⟶ X) :
    IsEffectiveCartierDivisor (Z.inverseImageSubspace g).ι ↔
      IsEffectiveCartierDivisor (Limits.pullback.snd Z.ι g) := by
  letI : IsClosedImmersion Z.ι := Z.isClosedImmersion
  let W : ClosedSubspace Y :=
    { X := Limits.pullback Z.ι g
      ι := Limits.pullback.snd Z.ι g
      isClosedImmersion :=
        IsClosedImmersion.of_isPullback (IsPullback.of_hasPullback Z.ι g).flip }
  have hI : (Z.inverseImageSubspace g).idealSheaf = W.idealSheaf :=
    (ClosedSubspace.overIso_iff_idealSheaf_eq _ _).mp
      ⟨Over.isoMk (inverseImage_isPullback g Z.ι).flip.isoPullback
        (IsPullback.isoPullback_hom_snd _)⟩
  constructor
  · intro h
    refine { toIsClosedImmersion := W.isClosedImmersion, invertibleIdealSheaf := ?_ }
    change MonoidalCategory.isInvertibleObject W.idealSheaf.toModule
    rw [← hI]
    exact h.invertibleIdealSheaf
  · intro h
    refine
      { toIsClosedImmersion := (Z.inverseImageSubspace g).isClosedImmersion
        invertibleIdealSheaf := ?_ }
    change MonoidalCategory.isInvertibleObject (Z.inverseImageSubspace g).idealSheaf.toModule
    rw [hI]
    exact h.invertibleIdealSheaf

/-- The inverse image of the center under its blowup is an effective Cartier divisor. -/
theorem inverseImage_isEffectiveCartier {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z) :
    IsEffectiveCartierDivisor (Z.inverseImageSubspace (Blowup.alongHom Z π)).ι := by
  letI : IsQuasiCoherent Z.idealSheaf :=
    @Hom.instIsQuasiCoherent_idealSheafSubobject S Z.X X Z.ι Z.isClosedImmersion
  obtain ⟨hE, _⟩ := (Blowup.properties π).2
  have hI : (exceptionalDivisor π).idealSheaf =
      (Z.inverseImageSubspace (Blowup.alongHom Z π)).idealSheaf := by
    simp only [exceptionalDivisor_spec, ClosedSubspace.inverseImage_idealSheaf,
      center, ClosedSubspace.ofQuasiCoherentIdeal_idealSheaf] <;> rfl
  refine
    { toIsClosedImmersion :=
        (Z.inverseImageSubspace (Blowup.alongHom Z π)).isClosedImmersion
      invertibleIdealSheaf := ?_ }
  change MonoidalCategory.isInvertibleObject
    (Z.inverseImageSubspace (Blowup.alongHom Z π)).idealSheaf.toModule
  rw [← hI]
  exact hE.invertibleIdealSheaf

/-- The blowup along `Z`, as an object of the full subcategory of spaces over `X`
whose inverse image of `Z` is an effective Cartier divisor. -/
def blowupObject {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    (π : along Z) : effectiveCartierPullbackOverCategory Z where
  obj := Over.mk (Blowup.alongHom Z π)
  property := inverseImage_isEffectiveCartier Z π

/-- The underlying slice object of the blowup object is its structure morphism. -/
theorem blowupObject_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z) :
    (blowupObject Z π).obj = Over.mk (Blowup.alongHom Z π) :=
  rfl

/-- The structure morphism of the blowup object is the blowup morphism. -/
theorem blowupObject_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z) :
    (blowupObject Z π).obj.hom = Blowup.alongHom Z π :=
  rfl

/-- The blowup object has effective Cartier inverse image of its center. -/
theorem blowupObject_property {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z) :
    IsEffectiveCartierDivisor (Z.inverseImageSubspace (blowupObject Z π).obj.hom).ι :=
  (blowupObject Z π).property

/-- A morphism whose inverse image of the center is an effective Cartier divisor
factors uniquely through the blowup morphism. -/
theorem existsUnique_lift {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Z : ClosedSubspace X} (π : along Z) {Y : AlgebraicSpace S} (g : Y ⟶ X)
    (hg : IsEffectiveCartierDivisor (Z.inverseImageSubspace g).ι) :
    ExistsUnique fun h : Y ⟶ Blowup.alongSpace Z π ↦ h ≫ Blowup.alongHom Z π = g :=
  sorry

/-- Every space over `X` with effective Cartier inverse image of `Z` admits a
unique morphism over `X` to the blowup along `Z`. -/
theorem existsUnique_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z)
    (Y : effectiveCartierPullbackOverCategory Z) :
    ExistsUnique fun f : Y ⟶ blowupObject Z π ↦
      f.hom.left ≫ Blowup.alongHom Z π = Y.obj.hom := by
  obtain ⟨h, hh, hu⟩ := existsUnique_lift π Y.obj.hom Y.property
  refine ⟨⟨Over.homMk h hh⟩, hh, ?_⟩
  intro f hf
  have he : f.hom.left = h := hu f.hom.left hf
  apply ObjectProperty.hom_ext
  exact Over.OverMorphism.ext he

/-- A morphism to the blowup object in the full subcategory commutes with the
structure morphisms to `X`. -/
theorem hom_w {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z)
    {Y : effectiveCartierPullbackOverCategory Z}
    (f : Y ⟶ blowupObject Z π) :
    f.hom.left ≫ Blowup.alongHom Z π = Y.obj.hom :=
  Over.w f.hom

end effectiveCartierPullbackOverCategory

namespace Blowup

/-- A Rees-Proj blowup along a closed subspace has the effective-Cartier
universal property. No blowup property is required from the caller. -/
theorem isBlowup_along {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z) :
    IsBlowup (alongHom Z π) Z where
  inverseImage_isEffectiveCartier :=
    (effectiveCartierPullbackOverCategory.inverseImage_isEffectiveCartier_iff_pullback
      Z (alongHom Z π)).mp
        (effectiveCartierPullbackOverCategory.inverseImage_isEffectiveCartier Z π)
  lift_unique g hg :=
    effectiveCartierPullbackOverCategory.existsUnique_lift π g
      ((effectiveCartierPullbackOverCategory.inverseImage_isEffectiveCartier_iff_pullback
        Z g).mpr hg)

/-- A closed subspace with ideal sheaf `I` is a center for every Rees blowup
in `I`. This transports only the property, retaining the supplied presentation. -/
theorem isBlowup_of_idealSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (Z : ClosedSubspace X)
    (hI : Z.idealSheaf = I) (π : Blowup X I) : IsBlowup π.hom Z := by
  subst I
  exact isBlowup_along Z π

/-- The Rees-Proj presentation in a quasi-coherent ideal defines a blowup in
the closed subspace cut out by that ideal. -/
theorem isBlowup {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I) :
    IsBlowup π.hom (center I) := by
  exact isBlowup_of_idealSheaf_eq (center I)
    (ClosedSubspace.ofQuasiCoherentIdeal_idealSheaf I) π

/-- Two lifts to a Rees blowup with the same structure morphism agree,
provided the inverse image of the center is effective Cartier. -/
theorem lift_hom_ext {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (g : Y ⟶ X)
    (hg : IsEffectiveCartierDivisor (Limits.pullback.snd (center I).ι g))
    {h k : Y ⟶ π.space} (hh : h ≫ π.hom = g) (hk : k ≫ π.hom = g) : h = k := by
  obtain ⟨l, _, hl⟩ := (isBlowup π).lift_unique g hg
  exact (hl h hh).trans (hl k hk).symm

/-- Precomposition of a lift is the lift of the composite whenever the
composite also has effective Cartier inverse image of the center. -/
theorem lift_comp {S : Scheme.{u}} {X Y W : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (g : Y ⟶ X) (f : W ⟶ Y)
    (hfg : IsEffectiveCartierDivisor (Limits.pullback.snd (center I).ι (f ≫ g)))
    (h : Y ⟶ π.space) (k : W ⟶ π.space)
    (hh : h ≫ π.hom = g) (hk : k ≫ π.hom = f ≫ g) : f ≫ h = k := by
  apply lift_hom_ext π (f ≫ g) hfg _ hk
  rw [Category.assoc, hh]

end Blowup

end AlgebraicGeometry.AlgebraicSpace
