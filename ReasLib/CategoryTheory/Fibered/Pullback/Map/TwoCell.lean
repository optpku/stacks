/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pullback.Map.Construction
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalTransformation

/-!
# Pullback on `2`-cells of fibred categories

This leaf owns the component, total, based, and bundled forms of the `2`-cell action along a
fixed base functor.
-/

@[expose] public section

noncomputable section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Limits
open scoped Bicategory

namespace FiberedCategoryOver.Pullback

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (u : C ⥤ D)

/-- Compatibility of a pulled-back `2`-cell component with the structural isomorphisms in the
categorical pullback. -/
theorem mapApp.compatibility
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) (x : CategoricalPullback u X.p) :
    u.map (𝟙 x.fst) ≫ ((totalMap u G).obj x).iso.hom =
      ((totalMap u F).obj x).iso.hom ≫
        Y.p.map ((FiberedCategoryOver.toNatTrans eta).app x.snd) := by
  letI : Y.p.IsHomLift (𝟙 (X.p.obj x.snd))
      ((FiberedCategoryOver.toNatTrans eta).app x.snd) :=
    eta.hom.isHomLift' x.snd
  have h : Y.p.map ((FiberedCategoryOver.toNatTrans eta).app x.snd) =
      eqToHom ((FiberedCategoryOver.toBasedFunctor F).w_obj x.snd) ≫
        eqToHom ((FiberedCategoryOver.toBasedFunctor G).w_obj x.snd).symm := by
    simpa only [Category.id_comp] using
      IsHomLift.fac' Y.p (𝟙 (X.p.obj x.snd))
        ((FiberedCategoryOver.toNatTrans eta).app x.snd)
  change u.map (𝟙 x.fst) ≫ (square u G).iso.hom.app x =
    (square u F).iso.hom.app x ≫ Y.p.map ((FiberedCategoryOver.toNatTrans eta).app x.snd)
  dsimp only [square, BasedFunctor.projectionIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_inv_app, eqToIso.inv, eqToHom_app]
  change u.map (𝟙 x.fst) ≫
      (x.iso.hom ≫
        eqToHom ((FiberedCategoryOver.toBasedFunctor G).w_obj x.snd).symm ≫ 𝟙 _) =
    (x.iso.hom ≫
      eqToHom ((FiberedCategoryOver.toBasedFunctor F).w_obj x.snd).symm ≫ 𝟙 _) ≫
        Y.p.map ((FiberedCategoryOver.toNatTrans eta).app x.snd)
  rw [h]
  simp only [Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl]

/-- The component of pullback on a `2`-cell. It is the identity on the base component and the
supplied vertical component on the total-category component. -/
noncomputable def mapApp
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) (x : CategoricalPullback u X.p) :
    (totalMap u F).obj x ⟶ (totalMap u G).obj x where
  fst := 𝟙 x.fst
  snd := (FiberedCategoryOver.toNatTrans eta).app x.snd
  w := mapApp.compatibility u eta x

/-- The base component of a pulled-back `2`-cell is the identity. -/
@[simp]
theorem mapApp.fst
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) (x : CategoricalPullback u X.p) :
    (mapApp u eta x).fst = 𝟙 x.fst := by
  rfl

/-- The total-category component of a pulled-back `2`-cell is the supplied vertical
transformation evaluated on the second pullback component. -/
@[simp]
theorem mapApp.snd
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) (x : CategoricalPullback u X.p) :
    (mapApp u eta x).snd =
      (FiberedCategoryOver.toNatTrans eta).app x.snd := by
  rfl

/-- The pulled-back `2`-cell components are natural in the categorical-pullback object. -/
theorem mapApp.naturality
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G)
    {x y : CategoricalPullback u X.p} (f : x ⟶ y) :
    (totalMap u F).map f ≫ mapApp u eta y =
      mapApp u eta x ≫ (totalMap u G).map f := by
  apply CategoricalPullback.hom_ext
  · change f.fst ≫ 𝟙 y.fst = 𝟙 x.fst ≫ f.fst
    rw [Category.comp_id, Category.id_comp]
  · change (FiberedCategoryOver.toFunctor F).map f.snd ≫
        (FiberedCategoryOver.toNatTrans eta).app y.snd =
      (FiberedCategoryOver.toNatTrans eta).app x.snd ≫
        (FiberedCategoryOver.toFunctor G).map f.snd
    exact (FiberedCategoryOver.toNatTrans eta).naturality f.snd

/-- Pullback of the underlying total natural transformation along `u`. -/
noncomputable def totalMap₂
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) : totalMap u F ⟶ totalMap u G where
  app := mapApp u eta
  naturality := fun {_ _} f ↦ mapApp.naturality u eta f

/-- The component of the total pulled-back transformation is `mapApp`. -/
@[simp]
theorem totalMap₂.app
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) (x : CategoricalPullback u X.p) :
    (totalMap₂ u eta).app x = mapApp u eta x := by
  rfl

/-- The total pulled-back `2`-cell lies over the identity of the base. -/
theorem totalMap₂.overId
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    eqToHom (basedMap u F).w.symm ≫
        Functor.whiskerRight (totalMap₂ u eta) (FiberedCategoryOver.pullback u Y).p ≫
          eqToHom (basedMap u G).w =
      𝟙 (FiberedCategoryOver.pullback u X).p := by
  apply NatTrans.ext
  funext x
  change eqToHom (rfl : x.fst = x.fst) ≫ 𝟙 x.fst ≫
    eqToHom (rfl : x.fst = x.fst) = 𝟙 x.fst
  simp only [eqToHom_refl, Category.id_comp]

/-- Pullback of the underlying based natural transformation along `u`. -/
noncomputable def basedMap₂
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) : basedMap u F ⟶ basedMap u G :=
  BasedNatTrans.ofOverId (totalMap₂ u eta) (totalMap₂.overId u eta)

/-- Forgetting the based packaging of a pulled-back `2`-cell recovers `totalMap₂`. -/
@[simp]
theorem basedMap₂.toNatTrans
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (basedMap₂ u eta).toNatTrans = totalMap₂ u eta := by
  rfl

/-- Pullback of a `2`-cell between morphisms of fibred categories. -/
noncomputable def map₂
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) : mapCanonical u F ⟶ mapCanonical u G :=
  FiberedCategoryOver.ofBasedNatTrans (basedMap₂ u eta)

/-- Forgetting a bundled pulled-back `2`-cell recovers its based natural transformation. -/
@[simp]
theorem map₂.toBasedNatTrans
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    FiberedCategoryOver.toBasedNatTrans (map₂ u eta) = basedMap₂ u eta := by
  rfl

/-- The total natural transformation of a pulled-back `2`-cell is `totalMap₂`. -/
@[simp]
theorem map₂.toNatTrans
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    FiberedCategoryOver.toNatTrans (map₂ u eta) = totalMap₂ u eta := by
  rfl

/-- The component of a pulled-back `2`-cell is `mapApp`. -/
@[simp]
theorem map₂.app
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) (x : CategoricalPullback u X.p) :
    (FiberedCategoryOver.toNatTrans (map₂ u eta)).app x = mapApp u eta x := by
  rw [map₂.toNatTrans u eta, totalMap₂.app u eta]

/-- The base component of a bundled pulled-back `2`-cell is the identity. -/
@[simp]
theorem map₂.app.fst
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) (x : CategoricalPullback u X.p) :
    ((FiberedCategoryOver.toNatTrans (map₂ u eta)).app x).fst =
      𝟙 x.fst := by
  rw [map₂.app u eta x, mapApp.fst]

/-- The total-category component of a bundled pulled-back `2`-cell is the original vertical
component on the second pullback coordinate. -/
@[simp]
theorem map₂.app.snd
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) (x : CategoricalPullback u X.p) :
    ((FiberedCategoryOver.toNatTrans (map₂ u eta)).app x).snd =
      (FiberedCategoryOver.toNatTrans eta).app x.snd := by
  rw [map₂.app u eta x, mapApp.snd]

/-- Pullback preserves identity `2`-cells. -/
@[simp]
theorem map₂.id
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    map₂ u (𝟙 F) = 𝟙 (mapCanonical u F) := by
  apply ObjectProperty.hom_ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  change mapApp u (𝟙 F) x = 𝟙 ((totalMap u F).obj x)
  apply CategoricalPullback.hom_ext
  · rfl
  · rfl

/-- Pullback preserves vertical composition of `2`-cells. -/
@[simp]
theorem map₂.comp
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G H : X ⟶ Y} (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂ u (eta ≫ theta) = map₂ u eta ≫ map₂ u theta := by
  apply ObjectProperty.hom_ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  change mapApp u (eta ≫ theta) x = mapApp u eta x ≫ mapApp u theta x
  apply CategoricalPullback.hom_ext
  · change 𝟙 x.fst = 𝟙 x.fst ≫ 𝟙 x.fst
    exact (Category.id_comp _).symm
  · rfl

end FiberedCategoryOver.Pullback

end CategoryTheory
