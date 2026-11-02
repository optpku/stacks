/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map

/-!
# Formal smoothness on objects for groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is formally
smooth on objects when every infinitesimal lifting problem against an affine
first-order thickening admits a solution whose restriction square commutes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace FormallySmoothOnObjects

/-- The 2-morphism `γ'|_U` obtained by restricting `γ' : x' ≫ p ≅ y'` along
`i : U ⟶ U'`: the associator `α_ (overMap i) x' p` followed by left whiskering
`overMap i ◁ γ'.hom`. -/
def restrictHom {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    {U U' : Over S} (i : U ⟶ U') {x' : GroupoidsOver.slice U' ⟶ X}
    {y' : GroupoidsOver.slice U' ⟶ Y} (γ' : x' ≫ p ≅ y') :
    slice.pullback i x' ≫ p ⟶ slice.pullback i y' :=
  (α_ (overMap i) x' p).hom ≫ (overMap i ◁ γ'.hom)

/-- `restrictHom p i γ'` is the composite of the associator and the left
whiskering of `γ'.hom` by `overMap i`. -/
theorem restrictHom_spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    {U U' : Over S} (i : U ⟶ U') {x' : GroupoidsOver.slice U' ⟶ X}
    {y' : GroupoidsOver.slice U' ⟶ Y} (γ' : x' ≫ p ≅ y') :
    restrictHom p i γ' = (α_ (overMap i) x' p).hom ≫ (overMap i ◁ γ'.hom) :=
  rfl

/-- The infinitesimal lifting square for `p` along `i`: `p(β)` followed by `γ`
equals the restriction `γ'|_U`. Here `slice.pullback i y'` is `y'|_U`,
`β.hom ▷ p` is `p(β)`, `restrictHom p i γ'` is `γ'|_U`, and the right-hand
vertical arrow of the square is the identity 2-cell. -/
def restrictionSquare {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    {U U' : Over S} (i : U ⟶ U') {x' : GroupoidsOver.slice U' ⟶ X}
    {y' : GroupoidsOver.slice U' ⟶ Y} {x : GroupoidsOver.slice U ⟶ X}
    (β : slice.pullback i x' ≅ x) (γ : x ≫ p ≅ slice.pullback i y')
    (γ' : x' ≫ p ≅ y') : Prop :=
  (β.hom ▷ p) ≫ γ.hom = restrictHom p i γ'

/-- `restrictionSquare` is the equality of `p(β)` followed by `γ` with
`γ'|_U`. -/
theorem restrictionSquare_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) {U U' : Over S} (i : U ⟶ U')
    {x' : GroupoidsOver.slice U' ⟶ X} {y' : GroupoidsOver.slice U' ⟶ Y}
    {x : GroupoidsOver.slice U ⟶ X} (β : slice.pullback i x' ≅ x)
    (γ : x ≫ p ≅ slice.pullback i y') (γ' : x' ≫ p ≅ y') :
    restrictionSquare p i β γ γ' ↔
      (β.hom ▷ p) ≫ γ.hom = restrictHom p i γ' :=
  Iff.rfl

/-- `restrictionSquare` is the commuting square with top arrow `γ'|_U`, left
arrow `p(β)`, bottom arrow `γ`, and right arrow the identity on `y'|_U`. -/
theorem restrictionSquare_commSq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) {U U' : Over S} (i : U ⟶ U')
    {x' : GroupoidsOver.slice U' ⟶ X} {y' : GroupoidsOver.slice U' ⟶ Y}
    {x : GroupoidsOver.slice U ⟶ X} (β : slice.pullback i x' ≅ x)
    (γ : x ≫ p ≅ slice.pullback i y') (γ' : x' ≫ p ≅ y') :
    restrictionSquare p i β γ γ' ↔
      CommSq (restrictHom p i γ') (β.hom ▷ p)
        (𝟙 (slice.pullback i y')) γ.hom :=
  by
    change ((β.hom ▷ p) ≫ γ.hom = restrictHom p i γ') ↔ _
    constructor
    · intro h
      exact ⟨by simpa only [Category.comp_id] using h.symm⟩
    · intro h
      simpa only [Category.comp_id] using h.w.symm

end FormallySmoothOnObjects

/-- A 1-morphism `p : X ⟶ Y` of categories fibred in groupoids over
`(Sch/S)_fppf` is formally smooth on objects when every infinitesimal lifting
problem against an affine first-order thickening admits a solution
`(x', β, γ')` making `restrictionSquare` commute. -/
class FormallySmoothOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) : Prop where
  /-- Affine first-order thickenings admit a lift `(x', β, γ')` whose
  restriction square commutes. -/
  exists_lift : ∀ {U U' : Over S} [IsAffine U.left] [IsAffine U'.left]
    (i : U ⟶ U') [IsFirstOrderThickening i.left]
    (y' : GroupoidsOver.slice U' ⟶ Y) (x : GroupoidsOver.slice U ⟶ X)
    (γ : x ≫ p ≅ slice.pullback i y'),
    ∃ (x' : GroupoidsOver.slice U' ⟶ X) (β : slice.pullback i x' ≅ x)
      (γ' : x' ≫ p ≅ y'), FormallySmoothOnObjects.restrictionSquare p i β γ γ'

namespace FormallySmoothOnObjects

/-- The identity 1-morphism of a category fibred in groupoids is formally
smooth on objects. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} :
    FormallySmoothOnObjects (𝟙 X) where
  exists_lift i _ y' x γ := by
    refine ⟨y', γ.symm ≪≫ ρ_ x, ρ_ y', ?_⟩
    set_option backward.isDefEq.respectTransparency false in
      simp [restrictionSquare, restrictHom, Category.assoc]
    rfl

/-- The composite of two 1-morphisms formally smooth on objects is formally
smooth on objects. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Y ⟶ Z) [FormallySmoothOnObjects p]
    [FormallySmoothOnObjects q] :
    FormallySmoothOnObjects (p ≫ q) where
  exists_lift i _ z' x γ := by
    rcases FormallySmoothOnObjects.exists_lift (p := q) i z' (x ≫ p)
      ((α_ x p q) ≪≫ γ) with ⟨y', βq, γq, hq⟩
    rcases FormallySmoothOnObjects.exists_lift (p := p) i y' x βq.symm with
      ⟨x', β, γp, hp⟩
    refine ⟨x', β, (α_ x' p q).symm ≪≫ (γp ▷ᵢ q) ≪≫ γq, ?_⟩
    change (β.hom ▷ p) ≫ βq.inv = restrictHom p i γp at hp
    have hp' : β.hom ▷ p = restrictHom p i γp ≫ βq.hom := by
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        congrArg (fun η => η ≫ βq.hom) hp
    change (βq.hom ▷ q) ≫ ((α_ x p q).hom ≫ γ.hom) =
      restrictHom q i γq at hq
    change (β.hom ▷ (p ≫ q)) ≫ γ.hom = _
    rw [Bicategory.whiskerRight_comp]
    simp only [Category.assoc]
    rw [hp', Bicategory.comp_whiskerRight]
    simp only [Category.assoc]
    rw [hq]
    change (α_ (overMap i ≫ x') p q).inv ≫
        ((α_ (overMap i) x' p).hom ≫ overMap i ◁ γp.hom) ▷ q ≫
        (α_ (overMap i) y' q).hom ≫ overMap i ◁ γq.hom =
      (α_ (overMap i) x' (p ≫ q)).hom ≫
        overMap i ◁ ((α_ x' p q).inv ≫ γp.hom ▷ q ≫ γq.hom)
    set_option backward.isDefEq.respectTransparency false in
      simp only [Bicategory.comp_whiskerRight, Bicategory.whiskerLeft_comp,
        Bicategory.whisker_assoc, Category.assoc, Iso.inv_hom_id_assoc,
        Bicategory.pentagon_inv_hom_hom_hom_inv_assoc]

/-- A formally smooth on objects 1-morphism lifts every affine first-order
infinitesimal lifting problem. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    [FormallySmoothOnObjects p] {U U' : Over S} [IsAffine U.left]
    [IsAffine U'.left] (i : U ⟶ U') [IsFirstOrderThickening i.left]
    (y' : GroupoidsOver.slice U' ⟶ Y) (x : GroupoidsOver.slice U ⟶ X)
    (γ : x ≫ p ≅ slice.pullback i y') :
    ∃ (x' : GroupoidsOver.slice U' ⟶ X) (β : slice.pullback i x' ≅ x)
      (γ' : x' ≫ p ≅ y'), restrictionSquare p i β γ γ' :=
  FormallySmoothOnObjects.exists_lift i y' x γ

/-- Formal smoothness on objects is the existence of a commuting restriction
square against every affine first-order thickening. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y) :
    FormallySmoothOnObjects p ↔
      ∀ {U U' : Over S} [IsAffine U.left] [IsAffine U'.left]
        (i : U ⟶ U') [IsFirstOrderThickening i.left]
        (y' : GroupoidsOver.slice U' ⟶ Y) (x : GroupoidsOver.slice U ⟶ X)
        (γ : x ≫ p ≅ slice.pullback i y'),
        ∃ (x' : GroupoidsOver.slice U' ⟶ X) (β : slice.pullback i x' ≅ x)
          (γ' : x' ≫ p ≅ y'), restrictionSquare p i β γ γ' :=
  ⟨fun h => h.exists_lift, fun h => ⟨h⟩⟩

end FormallySmoothOnObjects

end AlgebraicGeometry.Groupoids.Hom
