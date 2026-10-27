/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Comparison

/-!
# Mapping morphisms of readable pseudopullback cones

This module maps morphisms and `2`-morphisms of readable pseudopullback cones. Their comparison
modifications are obtained from generic pseudocone transport by conjugating at the three
walking-cospan vertices with the presentation comparisons.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uD vD wD

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} {D : Type uD}
variable [Bicategory.{wB, vB} B] [Bicategory.{wD, vD} D]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

namespace Implementation

/-- The components used to assemble the mapped comparison of a readable
pseudopullback-cone morphism. -/
private def mapPseudoPullbackCone.fac.app (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    ∀ j : LocallyDiscrete Limits.WalkingCospan,
      H.map (Bicategory.PseudoPullbackCone.map u) ≫
          (H.mapPseudoPullbackCone T).toPseudoCone.π.app j ⟶
        (H.mapPseudoPullbackCone S).toPseudoCone.π.app j
  | ⟨Limits.WalkingCospan.one⟩ =>
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.centerIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.one) ≫
        (mapPseudoPullbackCone.presentation.centerIso H S).inv
  | ⟨Limits.WalkingCospan.left⟩ =>
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.leftIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.left) ≫
        (mapPseudoPullbackCone.presentation.leftIso H S).inv
  | ⟨Limits.WalkingCospan.right⟩ =>
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.rightIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.right) ≫
        (mapPseudoPullbackCone.presentation.rightIso H S).inv

/-- The generic comparison at a vertex, with its structural unitors exposed. -/
private theorem generic_fac_app (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T)
    (j : LocallyDiscrete Limits.WalkingCospan) :
    (mapPseudoCone.fac H u.hom).as.app j =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (λ_ (H.map (T.toPseudoCone.π.app j))).hom ≫
        (H.mapComp (Bicategory.PseudoPullbackCone.map u)
          (T.toPseudoCone.π.app j)).inv ≫
        H.map₂ ((Bicategory.PseudoPullbackCone.fac u).as.app j) ≫
        (λ_ (H.map (S.toPseudoCone.π.app j))).inv := by
  change (α_ _ _ _).inv ≫
      ((ρ_ _).hom ≫ (λ_ _).inv) ▷ _ ≫
      (α_ _ _ _).hom ≫
      (𝟙 _) ◁ ((H.mapComp _ _).inv ≫ H.map₂ _) = _
  bicategory

/-- The left component after cancelling the presentation unitors. -/
private theorem mapped_fac_left (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    mapPseudoPullbackCone.fac.app H u
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      (H.mapComp (Bicategory.PseudoPullbackCone.map u) T.fst).inv ≫
        H.map₂ (Bicategory.PseudoPullbackCone.fstFac u) := by
  dsimp only [mapPseudoPullbackCone.fac.app]
  rw [generic_fac_app]
  change H.map (Bicategory.PseudoPullbackCone.map u) ◁ (λ_ (H.map T.fst)).inv ≫
      (H.map (Bicategory.PseudoPullbackCone.map u) ◁ (λ_ (H.map T.fst)).hom ≫
      (H.mapComp (Bicategory.PseudoPullbackCone.map u) T.fst).inv ≫
      H.map₂ (Bicategory.PseudoPullbackCone.fstFac u) ≫
      (λ_ (H.map S.fst)).inv) ≫ (λ_ (H.map S.fst)).hom = _
  simp

/-- The right component after cancelling the presentation unitors. -/
private theorem mapped_fac_right (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    mapPseudoPullbackCone.fac.app H u
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      (H.mapComp (Bicategory.PseudoPullbackCone.map u) T.snd).inv ≫
        H.map₂ (Bicategory.PseudoPullbackCone.sndFac u) := by
  dsimp only [mapPseudoPullbackCone.fac.app]
  rw [generic_fac_app]
  change H.map (Bicategory.PseudoPullbackCone.map u) ◁ (λ_ (H.map T.snd)).inv ≫
      (H.map (Bicategory.PseudoPullbackCone.map u) ◁ (λ_ (H.map T.snd)).hom ≫
      (H.mapComp (Bicategory.PseudoPullbackCone.map u) T.snd).inv ≫
      H.map₂ (Bicategory.PseudoPullbackCone.sndFac u) ≫
      (λ_ (H.map S.snd)).inv) ≫ (λ_ (H.map S.snd)).hom = _
  simp

/-- The central component after cancelling the presentation unitors. -/
private theorem mapped_fac_center (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    mapPseudoPullbackCone.fac.app H u
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁ (H.mapComp T.fst f).inv ≫
        (H.mapComp (Bicategory.PseudoPullbackCone.map u) (T.fst ≫ f)).inv ≫
        H.map₂ (Bicategory.PseudoPullbackCone.baseFac u) ≫
        (H.mapComp S.fst f).hom := by
  dsimp only [mapPseudoPullbackCone.fac.app]
  rw [generic_fac_app]
  change H.map (Bicategory.PseudoPullbackCone.map u) ◁
      ((H.mapComp T.fst f).inv ≫ (λ_ (H.map (T.fst ≫ f))).inv) ≫
      (H.map (Bicategory.PseudoPullbackCone.map u) ◁ (λ_ (H.map (T.fst ≫ f))).hom ≫
      (H.mapComp (Bicategory.PseudoPullbackCone.map u) (T.fst ≫ f)).inv ≫
      H.map₂ (Bicategory.PseudoPullbackCone.baseFac u) ≫
      (λ_ (H.map (S.fst ≫ f))).inv) ≫
      ((λ_ (H.map (S.fst ≫ f))).hom ≫ (H.mapComp S.fst f).hom) = _
  simp

/-- Naturality of the original comparison on the left generator, without unitors. -/
private theorem original_fac_left
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.baseFac u =
      (α_ (Bicategory.PseudoPullbackCone.map u) T.fst f).inv ≫
        Bicategory.PseudoPullbackCone.fstFac u ▷ f := by
  have h := (Bicategory.PseudoPullbackCone.fac u).as.naturality
    (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl)
  change 𝟙 _ ◁ Bicategory.PseudoPullbackCone.baseFac u ≫ (λ_ (S.fst ≫ f)).hom =
    ((α_ _ _ _).inv ≫
    ((λ_ (Bicategory.PseudoPullbackCone.map u)).hom ≫ (ρ_ _).inv) ▷ (T.fst ≫ f) ≫
    (α_ _ _ _).hom ≫
    Bicategory.PseudoPullbackCone.map u ◁ (λ_ (T.fst ≫ f)).hom ≫
    (α_ _ _ _).inv) ≫ Bicategory.PseudoPullbackCone.fstFac u ▷ f at h
  calc
    _ = (λ_ _).inv ≫
        (𝟙 _ ◁ Bicategory.PseudoPullbackCone.baseFac u ≫ (λ_ (S.fst ≫ f)).hom) := by
      bicategory
    _ = _ := by rw [h]; bicategory

/-- Naturality of the original comparison on the right generator, without unitors. -/
private theorem original_fac_right
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.baseFac u ≫ S.iso.hom =
      Bicategory.PseudoPullbackCone.map u ◁ T.iso.hom ≫
      (α_ (Bicategory.PseudoPullbackCone.map u) T.snd g).inv ≫
        Bicategory.PseudoPullbackCone.sndFac u ▷ g := by
  have h := (Bicategory.PseudoPullbackCone.fac u).as.naturality
    (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr)
  change 𝟙 _ ◁ Bicategory.PseudoPullbackCone.baseFac u ≫
    ((λ_ (S.fst ≫ f)).hom ≫ S.iso.hom) =
    ((α_ _ _ _).inv ≫
    ((λ_ (Bicategory.PseudoPullbackCone.map u)).hom ≫ (ρ_ _).inv) ▷ (T.fst ≫ f) ≫
    (α_ _ _ _).hom ≫
    Bicategory.PseudoPullbackCone.map u ◁ ((λ_ (T.fst ≫ f)).hom ≫ T.iso.hom) ≫
    (α_ _ _ _).inv) ≫ Bicategory.PseudoPullbackCone.sndFac u ▷ g at h
  calc
    _ = (λ_ _).inv ≫
        (𝟙 _ ◁ Bicategory.PseudoPullbackCone.baseFac u ≫
          ((λ_ (S.fst ≫ f)).hom ≫ S.iso.hom)) := by bicategory
    _ = _ := by rw [h]; bicategory

/-- The mapped central and left components satisfy the left-generator equation. -/
private theorem mapped_left_compat (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    mapPseudoPullbackCone.fac.app H u (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      (α_ (H.map (Bicategory.PseudoPullbackCone.map u)) (H.map T.fst) (H.map f)).inv ≫
        mapPseudoPullbackCone.fac.app H u
          (LocallyDiscrete.mk Limits.WalkingCospan.left) ▷ H.map f := by
  let l : S.pt ⟶ T.pt := Bicategory.PseudoPullbackCone.map u
  let a : l ≫ T.fst ⟶ S.fst := Bicategory.PseudoPullbackCone.fstFac u
  let c : l ≫ (T.fst ≫ f) ⟶ S.fst ≫ f := Bicategory.PseudoPullbackCone.baseFac u
  have hc : c = (α_ l T.fst f).inv ≫ a ▷ f := original_fac_left u
  rw [mapped_fac_center, mapped_fac_left]
  change H.map l ◁ (H.mapComp T.fst f).inv ≫ (H.mapComp l (T.fst ≫ f)).inv ≫
    H.map₂ c ≫ (H.mapComp S.fst f).hom =
    (α_ (H.map l) (H.map T.fst) (H.map f)).inv ≫
      ((H.mapComp l T.fst).inv ≫ H.map₂ a) ▷ H.map f
  rw [hc, H.map₂_comp, H.map₂_whisker_right,
    ← Category.assoc (H.map l ◁ (H.mapComp T.fst f).inv), H.mapComp_assoc_right_inv]
  simp only [Category.assoc, ← H.map₂_comp_assoc, Iso.hom_inv_id,
    H.map₂_id, Category.id_comp, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
    comp_whiskerRight]

/-- The mapped central and right components satisfy the right-generator equation. -/
private theorem mapped_right_compat (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    mapPseudoPullbackCone.fac.app H u (LocallyDiscrete.mk Limits.WalkingCospan.one) ≫
        (H.mapPseudoPullbackCone S).iso.hom =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁ (H.mapPseudoPullbackCone T).iso.hom ≫
        (α_ (H.map (Bicategory.PseudoPullbackCone.map u)) (H.map T.snd) (H.map g)).inv ≫
        mapPseudoPullbackCone.fac.app H u
          (LocallyDiscrete.mk Limits.WalkingCospan.right) ▷ H.map g := by
  let l : S.pt ⟶ T.pt := Bicategory.PseudoPullbackCone.map u
  let a : l ≫ T.snd ⟶ S.snd := Bicategory.PseudoPullbackCone.sndFac u
  let c : l ≫ (T.fst ≫ f) ⟶ S.fst ≫ f := Bicategory.PseudoPullbackCone.baseFac u
  have hc : c ≫ S.iso.hom = l ◁ T.iso.hom ≫ (α_ l T.snd g).inv ≫ a ▷ g :=
    original_fac_right u
  have ha : (H.mapComp l (T.snd ≫ g)).inv ≫ H.map₂ (α_ l T.snd g).inv ≫
      (H.mapComp (l ≫ T.snd) g).hom =
      H.map l ◁ (H.mapComp T.snd g).hom ≫
        (α_ (H.map l) (H.map T.snd) (H.map g)).inv ≫
        (H.mapComp l T.snd).inv ▷ H.map g := by
    apply (cancel_epi (H.map l ◁ (H.mapComp T.snd g).inv)).1
    rw [← Category.assoc (H.map l ◁ (H.mapComp T.snd g).inv), H.mapComp_assoc_right_inv]
    simp only [Category.assoc, ← H.map₂_comp_assoc, Iso.hom_inv_id,
      H.map₂_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id, whiskerLeft_inv_hom_assoc]
  rw [mapped_fac_center, mapped_fac_right]
  change (H.map l ◁ (H.mapComp T.fst f).inv ≫ (H.mapComp l (T.fst ≫ f)).inv ≫
      H.map₂ c ≫ (H.mapComp S.fst f).hom) ≫
      ((H.mapComp S.fst f).inv ≫ H.map₂ S.iso.hom ≫ (H.mapComp S.snd g).hom) =
    H.map l ◁ ((H.mapComp T.fst f).inv ≫ H.map₂ T.iso.hom ≫ (H.mapComp T.snd g).hom) ≫
      (α_ (H.map l) (H.map T.snd) (H.map g)).inv ≫
      ((H.mapComp l T.snd).inv ≫ H.map₂ a) ▷ H.map g
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← H.map₂_comp_assoc]
  rw [hc]
  simp only [H.map₂_comp, H.map₂_whisker_left, H.map₂_whisker_right,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc (H.map₂ (α_ l T.snd g).inv),
    ← Category.assoc (H.mapComp l (T.snd ≫ g)).inv, ha]
  simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]

/-- The conjugated generic comparison components satisfy modification naturality. -/
private theorem mapPseudoPullbackCone.fac.app.naturality
    (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b),
      (Pseudofunctor.const
          (LocallyDiscrete Limits.WalkingCospan) (H.obj S.pt)).map h ◁
            mapPseudoPullbackCone.fac.app H u b ≫
          ((H.mapPseudoPullbackCone S).toPseudoCone.π.naturality h).hom =
        ((((H.mapPseudoPullbackCone T).toPseudoCone.comparison
            (H.obj S.pt)).obj
              (H.map (Bicategory.PseudoPullbackCone.map u))).naturality h).hom ≫
          mapPseudoPullbackCone.fac.app H u a ▷
            (Bicategory.cospan (H.map f) (H.map g)).map h := by
  rintro ⟨a⟩ ⟨b⟩ ⟨h⟩
  cases h with
  | id a =>
      let s : H.obj S.pt ⟶ (cospan (H.map f) (H.map g)).obj (LocallyDiscrete.mk a) :=
        (H.mapPseudoPullbackCone S).toPseudoCone.π.app (LocallyDiscrete.mk a)
      let t : H.obj T.pt ⟶ (cospan (H.map f) (H.map g)).obj (LocallyDiscrete.mk a) :=
        (H.mapPseudoPullbackCone T).toPseudoCone.π.app (LocallyDiscrete.mk a)
      let m : H.map (Bicategory.PseudoPullbackCone.map u) ≫ t ⟶ s :=
        mapPseudoPullbackCone.fac.app H u (LocallyDiscrete.mk a)
      change 𝟙 _ ◁ m ≫ ((λ_ s).hom ≫ (ρ_ s).inv) =
        ((α_ _ _ _).inv ≫
          ((λ_ (H.map (Bicategory.PseudoPullbackCone.map u))).hom ≫ (ρ_ _).inv) ▷ t ≫
          (α_ _ _ _).hom ≫
          H.map (Bicategory.PseudoPullbackCone.map u) ◁ ((λ_ t).hom ≫ (ρ_ t).inv) ≫
          (α_ _ _ _).inv) ≫ m ▷ 𝟙 _
      bicategory
  | term j =>
      cases j with
      | left =>
          change 𝟙 _ ◁ mapPseudoPullbackCone.fac.app H u
              (LocallyDiscrete.mk Limits.WalkingCospan.one) ≫
              (λ_ (H.map S.fst ≫ H.map f)).hom =
            ((α_ _ _ _).inv ≫
              ((λ_ (H.map (Bicategory.PseudoPullbackCone.map u))).hom ≫ (ρ_ _).inv) ▷
                (H.map T.fst ≫ H.map f) ≫
              (α_ _ _ _).hom ≫
              H.map (Bicategory.PseudoPullbackCone.map u) ◁ (λ_ (H.map T.fst ≫ H.map f)).hom ≫
              (α_ _ _ _).inv) ≫
              mapPseudoPullbackCone.fac.app H u
                (LocallyDiscrete.mk Limits.WalkingCospan.left) ▷ H.map f
          rw [mapped_left_compat]
          bicategory
      | right =>
          have hc := mapped_right_compat H u
          change 𝟙 _ ◁ mapPseudoPullbackCone.fac.app H u
              (LocallyDiscrete.mk Limits.WalkingCospan.one) ≫
              ((λ_ (H.map S.fst ≫ H.map f)).hom ≫ (H.mapPseudoPullbackCone S).iso.hom) =
            ((α_ _ _ _).inv ≫
              ((λ_ (H.map (Bicategory.PseudoPullbackCone.map u))).hom ≫ (ρ_ _).inv) ▷
                (H.map T.fst ≫ H.map f) ≫
              (α_ _ _ _).hom ≫
              H.map (Bicategory.PseudoPullbackCone.map u) ◁
                ((λ_ (H.map T.fst ≫ H.map f)).hom ≫ (H.mapPseudoPullbackCone T).iso.hom) ≫
              (α_ _ _ _).inv) ≫
              mapPseudoPullbackCone.fac.app H u
                (LocallyDiscrete.mk Limits.WalkingCospan.right) ▷ H.map g
          calc
            _ = (λ_ _).hom ≫
                (mapPseudoPullbackCone.fac.app H u
                    (LocallyDiscrete.mk Limits.WalkingCospan.one) ≫
                  (H.mapPseudoPullbackCone S).iso.hom) := by bicategory
            _ = _ := by rw [hc]; bicategory

end Implementation

/-- The comparison modification carried by a mapped readable pseudopullback-cone morphism.

Its three components are the generic mapped comparison conjugated by the corresponding
presentation isomorphisms, so this readable facade introduces no second transport convention. -/
def mapPseudoPullbackCone.fac (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    ((H.mapPseudoPullbackCone T).toPseudoCone.comparison
        (H.obj S.pt)).obj
          (H.map (Bicategory.PseudoPullbackCone.map u)) ⟶
      (H.mapPseudoPullbackCone S).toPseudoCone.π :=
  ⟨{
    app := Implementation.mapPseudoPullbackCone.fac.app H u
    naturality := Implementation.mapPseudoPullbackCone.fac.app.naturality H u }⟩

/-- The left component of the readable mapped comparison is the generic comparison conjugated
by the left-vertex presentation isomorphisms. -/
@[simp]
theorem mapPseudoPullbackCone.fac.app.left (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    (mapPseudoPullbackCone.fac H u).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.leftIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.left) ≫
        (mapPseudoPullbackCone.presentation.leftIso H S).inv := by
  rfl

/-- The right component of the readable mapped comparison is the generic comparison conjugated
by the right-vertex presentation isomorphisms. -/
@[simp]
theorem mapPseudoPullbackCone.fac.app.right (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    (mapPseudoPullbackCone.fac H u).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.rightIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.right) ≫
        (mapPseudoPullbackCone.presentation.rightIso H S).inv := by
  rfl

/-- The central component of the readable mapped comparison is the generic comparison
conjugated by the central presentation isomorphisms. -/
@[simp]
theorem mapPseudoPullbackCone.fac.app.center (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    (mapPseudoPullbackCone.fac H u).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.centerIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.one) ≫
        (mapPseudoPullbackCone.presentation.centerIso H S).inv := by
  rfl

/-- Map a morphism of readable pseudopullback cones along a pseudofunctor. Its apex map is the
image of the original apex map, and its comparison is `mapPseudoPullbackCone.fac`. -/
def mapPseudoPullbackCone.map (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    H.mapPseudoPullbackCone S ⟶ H.mapPseudoPullbackCone T :=
  Bicategory.PseudoPullbackCone.homMk
    (H.map (Bicategory.PseudoPullbackCone.map u))
    (mapPseudoPullbackCone.fac H u)

/-- The apex map of a mapped readable pseudopullback-cone morphism. -/
@[simp]
theorem mapPseudoPullbackCone.map.apex (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.map (mapPseudoPullbackCone.map H u) =
      H.map (Bicategory.PseudoPullbackCone.map u) := by
  rfl

/-- The comparison modification of a mapped readable pseudopullback-cone morphism. -/
@[simp]
theorem mapPseudoPullbackCone.map.fac (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.fac (mapPseudoPullbackCone.map H u) =
      mapPseudoPullbackCone.fac H u := by
  apply StrongTrans.homCategory.ext
  intro j
  change ((mapPseudoPullbackCone.fac H u).as.app j ≫ (ρ_ _).inv) ≫ (ρ_ _).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The left-leg comparison cell of a mapped readable pseudopullback-cone morphism. -/
@[simp]
theorem mapPseudoPullbackCone.map.fstFac (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.fstFac (mapPseudoPullbackCone.map H u) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.leftIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.left) ≫
        (mapPseudoPullbackCone.presentation.leftIso H S).inv := by
  change (Bicategory.PseudoPullbackCone.fac (mapPseudoPullbackCone.map H u)).as.app
    (LocallyDiscrete.mk Limits.WalkingCospan.left) = _
  rw [mapPseudoPullbackCone.map.fac]
  rfl

/-- The right-leg comparison cell of a mapped readable pseudopullback-cone morphism. -/
@[simp]
theorem mapPseudoPullbackCone.map.sndFac (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    Bicategory.PseudoPullbackCone.sndFac (mapPseudoPullbackCone.map H u) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁
          (mapPseudoPullbackCone.presentation.rightIso H T).hom ≫
        (mapPseudoCone.fac H u.hom).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.right) ≫
        (mapPseudoPullbackCone.presentation.rightIso H S).inv := by
  change (Bicategory.PseudoPullbackCone.fac (mapPseudoPullbackCone.map H u)).as.app
    (LocallyDiscrete.mk Limits.WalkingCospan.right) = _
  rw [mapPseudoPullbackCone.map.fac]
  rfl

namespace Implementation

/-- The original apex cell satisfies the normalized comparison equation at each vertex. -/
private theorem normalized_cell_app
    {S T : Bicategory.PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v)
    (j : LocallyDiscrete Limits.WalkingCospan) :
    Bicategory.PseudoPullbackCone.map₂ η ▷ T.toPseudoCone.π.app j ≫
        (Bicategory.PseudoPullbackCone.fac v).as.app j =
      (Bicategory.PseudoPullbackCone.fac u).as.app j := by
  let s : S.pt ⟶ (cospan f g).obj j := S.toPseudoCone.π.app j
  let t : T.pt ⟶ (cospan f g).obj j := T.toPseudoCone.π.app j
  let a : Bicategory.PseudoPullbackCone.map u ≫ t ⟶ s ≫ 𝟙 _ := u.hom.cell.as.app j
  let b : Bicategory.PseudoPullbackCone.map v ≫ t ⟶ s ≫ 𝟙 _ := v.hom.cell.as.app j
  have h := congrArg (fun Γ => Γ.as.app j) η.hom.w
  change Bicategory.PseudoPullbackCone.map₂ η ▷ t ≫ b = a ≫ s ◁ 𝟙 (𝟙 _) at h
  simp only [whiskerLeft_id, Category.comp_id] at h
  change _ ▷ t ≫ (b ≫ (ρ_ s).hom) = a ≫ (ρ_ s).hom
  rw [← Category.assoc, h]

/-- Mapping and conjugating the normalized equation preserves its commutativity. -/
private theorem generic_cell_compatible (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v)
    (j : LocallyDiscrete Limits.WalkingCospan) :
    H.map₂ (Bicategory.PseudoPullbackCone.map₂ η) ▷
          (mapPseudoCone H T.toPseudoCone).π.app j ≫
        (mapPseudoCone.fac H v.hom).as.app j =
      (mapPseudoCone.fac H u.hom).as.app j := by
  let s : S.pt ⟶ (cospan f g).obj j := S.toPseudoCone.π.app j
  let t : T.pt ⟶ (cospan f g).obj j := T.toPseudoCone.π.app j
  let a : Bicategory.PseudoPullbackCone.map u ≫ t ⟶ s :=
    (Bicategory.PseudoPullbackCone.fac u).as.app j
  let b : Bicategory.PseudoPullbackCone.map v ≫ t ⟶ s :=
    (Bicategory.PseudoPullbackCone.fac v).as.app j
  have hc : Bicategory.PseudoPullbackCone.map₂ η ▷ t ≫ b = a := normalized_cell_app η j
  have hn : (H.mapComp (Bicategory.PseudoPullbackCone.map u) t).inv ≫
      H.map₂ (Bicategory.PseudoPullbackCone.map₂ η ▷ t) =
      H.map₂ (Bicategory.PseudoPullbackCone.map₂ η) ▷ H.map t ≫
      (H.mapComp (Bicategory.PseudoPullbackCone.map v) t).inv :=
    H.toLax.mapComp_naturality_left _ _
  rw [generic_fac_app, generic_fac_app]
  change H.map₂ (Bicategory.PseudoPullbackCone.map₂ η) ▷ (𝟙 _ ≫ H.map t) ≫
      (H.map (Bicategory.PseudoPullbackCone.map v) ◁ (λ_ (H.map t)).hom ≫
        (H.mapComp (Bicategory.PseudoPullbackCone.map v) t).inv ≫ H.map₂ b ≫
        (λ_ (H.map s)).inv) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁ (λ_ (H.map t)).hom ≫
        (H.mapComp (Bicategory.PseudoPullbackCone.map u) t).inv ≫ H.map₂ a ≫
        (λ_ (H.map s)).inv
  calc
    _ = H.map (Bicategory.PseudoPullbackCone.map u) ◁ (λ_ (H.map t)).hom ≫
        (H.map₂ (Bicategory.PseudoPullbackCone.map₂ η) ▷ H.map t ≫
          (H.mapComp (Bicategory.PseudoPullbackCone.map v) t).inv) ≫
        H.map₂ b ≫ (λ_ (H.map s)).inv := by bicategory
    _ = _ := by
      rw [← hn]
      simp only [Category.assoc, ← H.map₂_comp_assoc, hc]

private theorem conjugated_cell_compatible (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v)
    (j : LocallyDiscrete Limits.WalkingCospan)
    {s : H.obj S.pt ⟶ H.obj ((cospan f g).obj j)}
    {t : H.obj T.pt ⟶ H.obj ((cospan f g).obj j)}
    (eS : s ≅ (mapPseudoCone H S.toPseudoCone).π.app j)
    (eT : t ≅ (mapPseudoCone H T.toPseudoCone).π.app j) :
    H.map₂ (Bicategory.PseudoPullbackCone.map₂ η) ▷ t ≫
        (H.map (Bicategory.PseudoPullbackCone.map v) ◁ eT.hom ≫
          (mapPseudoCone.fac H v.hom).as.app j ≫ eS.inv) =
      H.map (Bicategory.PseudoPullbackCone.map u) ◁ eT.hom ≫
        (mapPseudoCone.fac H u.hom).as.app j ≫ eS.inv := by
  let s' : H.obj S.pt ⟶ H.obj ((cospan f g).obj j) :=
    (mapPseudoCone H S.toPseudoCone).π.app j
  let t' : H.obj T.pt ⟶ H.obj ((cospan f g).obj j) :=
    (mapPseudoCone H T.toPseudoCone).π.app j
  let a : H.map (Bicategory.PseudoPullbackCone.map u) ≫ t' ⟶ s' :=
    (mapPseudoCone.fac H u.hom).as.app j
  let b : H.map (Bicategory.PseudoPullbackCone.map v) ≫ t' ⟶ s' :=
    (mapPseudoCone.fac H v.hom).as.app j
  have hc : H.map₂ (Bicategory.PseudoPullbackCone.map₂ η) ▷ t' ≫ b = a :=
    generic_cell_compatible H η j
  change _ ▷ t ≫ (_ ◁ eT.hom ≫ b ≫ eS.inv) = _ ◁ eT.hom ≫ a ≫ eS.inv
  rw [← Category.assoc, ← whisker_exchange]
  simp only [Category.assoc]
  rw [← Category.assoc (H.map₂ (Bicategory.PseudoPullbackCone.map₂ η) ▷ t'), hc]

/-- Compatibility of the mapped readable apex cell with the conjugated comparison
modifications. -/
private theorem mapPseudoPullbackCone.map₂.comm (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    ((H.mapPseudoPullbackCone T).toPseudoCone.comparison
        (H.obj S.pt)).map
          (H.map₂ (Bicategory.PseudoPullbackCone.map₂ η)) ≫
        Bicategory.PseudoPullbackCone.fac
          (mapPseudoPullbackCone.map H v) =
      Bicategory.PseudoPullbackCone.fac
        (mapPseudoPullbackCone.map H u) := by
  rw [mapPseudoPullbackCone.map.fac, mapPseudoPullbackCone.map.fac]
  apply StrongTrans.homCategory.ext
  rintro ⟨j⟩
  cases j with
  | none =>
      exact conjugated_cell_compatible H η (LocallyDiscrete.mk Limits.WalkingCospan.one)
        (mapPseudoPullbackCone.presentation.centerIso H S)
        (mapPseudoPullbackCone.presentation.centerIso H T)
  | some j =>
      cases j with
      | left =>
          exact conjugated_cell_compatible H η (LocallyDiscrete.mk Limits.WalkingCospan.left)
            (mapPseudoPullbackCone.presentation.leftIso H S)
            (mapPseudoPullbackCone.presentation.leftIso H T)
      | right =>
          exact conjugated_cell_compatible H η (LocallyDiscrete.mk Limits.WalkingCospan.right)
            (mapPseudoPullbackCone.presentation.rightIso H S)
            (mapPseudoPullbackCone.presentation.rightIso H T)

end Implementation

/-- Map a `2`-morphism of readable pseudopullback cones along a pseudofunctor. Its apex cell is
the image of the original apex cell. -/
def mapPseudoPullbackCone.map₂ (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    mapPseudoPullbackCone.map H u ⟶ mapPseudoPullbackCone.map H v :=
  Bicategory.PseudoPullbackCone.hom₂Mk
    (H.map₂ (Bicategory.PseudoPullbackCone.map₂ η))
    (Implementation.mapPseudoPullbackCone.map₂.comm H η)

/-- The apex cell of a mapped readable pseudopullback-cone `2`-morphism. -/
@[simp]
theorem mapPseudoPullbackCone.map₂.apex (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    Bicategory.PseudoPullbackCone.map₂
        (mapPseudoPullbackCone.map₂ H η) =
      H.map₂ (Bicategory.PseudoPullbackCone.map₂ η) := by
  rfl

-- Data audit: every component of `mapPseudoPullbackCone.fac` is an explicit conjugate of
-- `mapPseudoCone.fac`; the apex data of `mapPseudoPullbackCone.map` and
-- `mapPseudoPullbackCone.map₂` are respectively `H.map` and `H.map₂` of the original apex
-- data. Their `sorryAx` dependencies are confined to naturality and compatibility propositions.

end Pseudofunctor

end CategoryTheory
