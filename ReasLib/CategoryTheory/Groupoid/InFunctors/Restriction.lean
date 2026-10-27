/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.Groupoid.InFunctors

/-!
# Restriction of groupoids in functors

Restriction of a groupoid in functors along a functor `ι : C' ⥤ C` (in particular, along
a subcategory inclusion) is precomposition on object/arrow functors and left whiskering on
structure maps, with composition transported by the pullback-preservation isomorphism.
-/

@[expose] public section

open CategoryTheory Functor Limits

noncomputable section

universe u u' u'' v v' v'' w

namespace CategoryTheory.GroupoidInFunctors

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [HasPullbacks (C ⥤ Type w)]

/-- The first projection of a pullback transported through precomposition. -/
@[reassoc (attr := simp)]
private theorem restrict_pullback_inv_fst {C' : Type u'} [Category.{v'} C']
    [HasPullbacks (C' ⥤ Type w)] (ι : C' ⥤ C)
    {X Y Z : C ⥤ Type w} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) f g).inv ≫
        whiskerLeft ι (pullback.fst f g) =
      pullback.fst (whiskerLeft ι f) (whiskerLeft ι g) :=
  PreservesPullback.iso_inv_fst _ _ _

/-- The second projection of a pullback transported through precomposition. -/
@[reassoc (attr := simp)]
private theorem restrict_pullback_inv_snd {C' : Type u'} [Category.{v'} C']
    [HasPullbacks (C' ⥤ Type w)] (ι : C' ⥤ C)
    {X Y Z : C ⥤ Type w} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) f g).inv ≫
        whiskerLeft ι (pullback.snd f g) =
      pullback.snd (whiskerLeft ι f) (whiskerLeft ι g) :=
  PreservesPullback.iso_inv_snd _ _ _

/-- The source of a restricted composite is the source of its earlier arrow. -/
private theorem restrict_comp_source {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) ≫ (whiskerLeft ι G.s) =
      pullback.snd (whiskerLeft ι G.s) (whiskerLeft ι G.t) ≫ whiskerLeft ι G.s := by
  rw [Category.assoc, ← whiskerLeft_comp, G.comp_source, whiskerLeft_comp,
    ← Category.assoc, restrict_pullback_inv_snd]

/-- The target of a restricted composite is the target of its later arrow. -/
private theorem restrict_comp_target {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) ≫ (whiskerLeft ι G.t) =
      pullback.fst (whiskerLeft ι G.s) (whiskerLeft ι G.t) ≫ whiskerLeft ι G.t := by
  rw [Category.assoc, ← whiskerLeft_comp, G.comp_target, whiskerLeft_comp,
    ← Category.assoc, restrict_pullback_inv_fst]

/-- In the precomposed groupoid, identity arrows have the specified source. -/
private theorem restrict_identity_source {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (whiskerLeft ι G.e) ≫ (whiskerLeft ι G.s) = 𝟙 (ι ⋙ G.U) := by
  rw [← whiskerLeft_comp, G.identity_source, whiskerLeft_id']

/-- In the precomposed groupoid, identity arrows have the specified target. -/
private theorem restrict_identity_target {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (whiskerLeft ι G.e) ≫ (whiskerLeft ι G.t) = 𝟙 (ι ⋙ G.U) := by
  rw [← whiskerLeft_comp, G.identity_target, whiskerLeft_id']

/-- In the precomposed groupoid, inversion exchanges source with target. -/
private theorem restrict_inverse_source {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (whiskerLeft ι G.i) ≫ (whiskerLeft ι G.s) = whiskerLeft ι G.t := by
  rw [← whiskerLeft_comp, G.inverse_source]

/-- In the precomposed groupoid, inversion exchanges target with source. -/
private theorem restrict_inverse_target {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (whiskerLeft ι G.i) ≫ (whiskerLeft ι G.t) = whiskerLeft ι G.s := by
  rw [← whiskerLeft_comp, G.inverse_target]

/-- Transport a pullback lift, then precompose by an arbitrary generalized element. -/
private theorem restrict_lift_comp {C' : Type u'} [Category.{v'} C']
    [HasPullbacks (C' ⥤ Type w)] (ι : C' ⥤ C)
    {V X Y Z Q : C ⥤ Type w} (f : X ⟶ Z) (g : Y ⟶ Z)
    (c : pullback f g ⟶ Q) {W : C' ⥤ Type w} (p : W ⟶ ι ⋙ V)
    (a : V ⟶ X) (b : V ⟶ Y) (h : a ≫ f = b ≫ g)
    (h' : (p ≫ whiskerLeft ι a) ≫ whiskerLeft ι f =
      (p ≫ whiskerLeft ι b) ≫ whiskerLeft ι g) :
    pullback.lift (p ≫ whiskerLeft ι a) (p ≫ whiskerLeft ι b) h' ≫
        ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) f g).inv ≫
          whiskerLeft ι c) =
      p ≫ whiskerLeft ι (pullback.lift a b h ≫ c) := by
  have hlift : pullback.lift (p ≫ whiskerLeft ι a) (p ≫ whiskerLeft ι b) h' ≫
      (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) f g).inv =
        p ≫ whiskerLeft ι (pullback.lift a b h) := by
    apply (cancel_mono
      (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) f g).hom).1
    apply pullback.hom_ext
    · simp [Category.assoc, ← whiskerLeft_comp]
    · simp [Category.assoc, ← whiskerLeft_comp]
  rw [← Category.assoc, hlift, Category.assoc, ← whiskerLeft_comp]

/-- In the precomposed groupoid, composition is associative on generalized arrows. -/
private theorem restrict_associativity {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    ∀ {W : C' ⥤ Type w} (a b d : W ⟶ (ι ⋙ G.R))
      (h_ab : a ≫ (whiskerLeft ι G.s) = b ≫ (whiskerLeft ι G.t))
      (h_bd : b ≫ (whiskerLeft ι G.s) = d ≫ (whiskerLeft ι G.t))
      (h_ab_d : (pullback.lift a b h_ab ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c)) ≫ (whiskerLeft ι G.s) = d ≫ (whiskerLeft ι G.t))
      (h_a_bd : a ≫ (whiskerLeft ι G.s) = (pullback.lift b d h_bd ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c)) ≫ (whiskerLeft ι G.t)),
      pullback.lift (pullback.lift a b h_ab ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c)) d h_ab_d ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) =
        pullback.lift a (pullback.lift b d h_bd ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c)) h_a_bd ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) := by
  intro W a b d h_ab h_bd h_ab_d h_a_bd
  -- A pair of composable arrows, followed by a third arrow.
  let σ := pullback.snd G.s G.t ≫ G.s
  let x := pullback.fst σ G.t ≫ pullback.fst G.s G.t
  let y := pullback.fst σ G.t ≫ pullback.snd G.s G.t
  let z := pullback.snd σ G.t
  have hxy : x ≫ G.s = y ≫ G.t := by
    simp only [x, y, Category.assoc, pullback.condition]
  have hyz : y ≫ G.s = z ≫ G.t := by
    simpa only [y, z, σ, Category.assoc] using
      (pullback.condition (f := σ) (g := G.t))
  have hxy_z : (pullback.lift x y hxy ≫ G.c) ≫ G.s = z ≫ G.t := by
    simpa only [Category.assoc, G.comp_source, pullback.lift_snd_assoc] using hyz
  have hx_yz : x ≫ G.s = (pullback.lift y z hyz ≫ G.c) ≫ G.t := by
    simpa only [Category.assoc, G.comp_target, pullback.lift_fst_assoc] using hxy
  -- Factor the three given arrows through the restriction of this universal triple.
  let p_ab := pullback.lift a b h_ab ≫
    (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv
  have hp_ab : p_ab ≫ whiskerLeft ι σ = d ≫ whiskerLeft ι G.t := by
    simpa only [p_ab, σ, whiskerLeft_comp, Category.assoc,
      restrict_pullback_inv_snd_assoc, pullback.lift_snd_assoc] using h_bd
  let p := pullback.lift p_ab d hp_ab ≫
    (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) σ G.t).inv
  have hpx : p ≫ whiskerLeft ι x = a := by
    simp [p, x, p_ab, whiskerLeft_comp, Category.assoc]
  have hpy : p ≫ whiskerLeft ι y = b := by
    simp [p, y, p_ab, whiskerLeft_comp, Category.assoc]
  have hpz : p ≫ whiskerLeft ι z = d := by
    simp [p, z, Category.assoc]
  let c' := (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
    whiskerLeft ι G.c
  have hxy_map : pullback.lift a b h_ab ≫ c' =
      p ≫ whiskerLeft ι (pullback.lift x y hxy ≫ G.c) := by
    simpa only [hpx, hpy] using
      (restrict_lift_comp ι G.s G.t G.c p x y hxy
        (by rw [hpx, hpy]; exact h_ab))
  have hyz_map : pullback.lift b d h_bd ≫ c' =
      p ≫ whiskerLeft ι (pullback.lift y z hyz ≫ G.c) := by
    simpa only [hpy, hpz] using
      (restrict_lift_comp ι G.s G.t G.c p y z hyz
        (by rw [hpy, hpz]; exact h_bd))
  have hleft : pullback.lift (pullback.lift a b h_ab ≫ c') d h_ab_d ≫ c' =
      p ≫ whiskerLeft ι
        (pullback.lift (pullback.lift x y hxy ≫ G.c) z hxy_z ≫ G.c) := by
    simpa only [← hxy_map, hpz] using
      (restrict_lift_comp ι G.s G.t G.c p (pullback.lift x y hxy ≫ G.c) z hxy_z
        (by rw [← hxy_map, hpz]; exact h_ab_d))
  have hright : pullback.lift a (pullback.lift b d h_bd ≫ c') h_a_bd ≫ c' =
      p ≫ whiskerLeft ι
        (pullback.lift x (pullback.lift y z hyz ≫ G.c) hx_yz ≫ G.c) := by
    simpa only [hpx, ← hyz_map] using
      (restrict_lift_comp ι G.s G.t G.c p x (pullback.lift y z hyz ≫ G.c) hx_yz
        (by rw [hpx, ← hyz_map]; exact h_a_bd))
  calc
    _ = p ≫ whiskerLeft ι
        (pullback.lift (pullback.lift x y hxy ≫ G.c) z hxy_z ≫ G.c) := hleft
    _ = p ≫ whiskerLeft ι
        (pullback.lift x (pullback.lift y z hyz ≫ G.c) hx_yz ≫ G.c) := by
      rw [G.associativity x y z hxy hyz hxy_z hx_yz]
    _ = _ := hright.symm

/-- In the precomposed groupoid, composing an arrow with the identity at its source does not change it. -/
private theorem restrict_right_identity {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    ∀ {W : C' ⥤ Type w} (a : W ⟶ (ι ⋙ G.R))
      (h : a ≫ (whiskerLeft ι G.s) = ((a ≫ (whiskerLeft ι G.s)) ≫ (whiskerLeft ι G.e)) ≫ (whiskerLeft ι G.t)),
      pullback.lift a ((a ≫ (whiskerLeft ι G.s)) ≫ (whiskerLeft ι G.e)) h ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) = a := by
  intro W a h
  have h₀ : 𝟙 G.R ≫ G.s = ((𝟙 G.R ≫ G.s) ≫ G.e) ≫ G.t := by
    simp [Category.assoc, G.identity_target]
  calc
    _ = a ≫ whiskerLeft ι
        (pullback.lift (𝟙 G.R) ((𝟙 G.R ≫ G.s) ≫ G.e) h₀ ≫ G.c) := by
      simpa only [Category.id_comp, whiskerLeft_id', Category.comp_id,
        whiskerLeft_comp, Category.assoc] using
        (restrict_lift_comp ι G.s G.t G.c a (𝟙 G.R) ((𝟙 G.R ≫ G.s) ≫ G.e) h₀
          (by simpa only [Category.id_comp, whiskerLeft_id', Category.comp_id,
            whiskerLeft_comp, Category.assoc] using h))
    _ = a := by rw [G.right_identity (𝟙 G.R) h₀, whiskerLeft_id', Category.comp_id]

/-- In the precomposed groupoid, composing the identity at the target of an arrow with that arrow does not change it. -/
private theorem restrict_left_identity {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    ∀ {W : C' ⥤ Type w} (a : W ⟶ (ι ⋙ G.R))
      (h : ((a ≫ (whiskerLeft ι G.t)) ≫ (whiskerLeft ι G.e)) ≫ (whiskerLeft ι G.s) = a ≫ (whiskerLeft ι G.t)),
      pullback.lift ((a ≫ (whiskerLeft ι G.t)) ≫ (whiskerLeft ι G.e)) a h ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) = a := by
  intro W a h
  have h₀ : ((𝟙 G.R ≫ G.t) ≫ G.e) ≫ G.s = 𝟙 G.R ≫ G.t := by
    simp [Category.assoc, G.identity_source]
  calc
    _ = a ≫ whiskerLeft ι
        (pullback.lift ((𝟙 G.R ≫ G.t) ≫ G.e) (𝟙 G.R) h₀ ≫ G.c) := by
      simpa only [Category.id_comp, whiskerLeft_id', Category.comp_id,
        whiskerLeft_comp, Category.assoc] using
        (restrict_lift_comp ι G.s G.t G.c a ((𝟙 G.R ≫ G.t) ≫ G.e) (𝟙 G.R) h₀
          (by simpa only [Category.id_comp, whiskerLeft_id', Category.comp_id,
            whiskerLeft_comp, Category.assoc] using h))
    _ = a := by rw [G.left_identity (𝟙 G.R) h₀, whiskerLeft_id', Category.comp_id]

/-- In the precomposed groupoid, composing an arrow after its inverse gives the identity at its target. -/
private theorem restrict_inverse_comp {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    ∀ {W : C' ⥤ Type w} (a : W ⟶ (ι ⋙ G.R))
      (h : a ≫ (whiskerLeft ι G.s) = (a ≫ (whiskerLeft ι G.i)) ≫ (whiskerLeft ι G.t)),
      pullback.lift a (a ≫ (whiskerLeft ι G.i)) h ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) = (a ≫ (whiskerLeft ι G.t)) ≫ (whiskerLeft ι G.e) := by
  intro W a h
  have h₀ : 𝟙 G.R ≫ G.s = (𝟙 G.R ≫ G.i) ≫ G.t := by
    simp [G.inverse_target]
  calc
    _ = a ≫ whiskerLeft ι
        (pullback.lift (𝟙 G.R) (𝟙 G.R ≫ G.i) h₀ ≫ G.c) := by
      simpa only [Category.id_comp, whiskerLeft_id', Category.comp_id] using
        (restrict_lift_comp ι G.s G.t G.c a (𝟙 G.R) (𝟙 G.R ≫ G.i) h₀
          (by simpa only [Category.id_comp, whiskerLeft_id', Category.comp_id] using h))
    _ = _ := by
      rw [G.inverse_comp (𝟙 G.R) h₀, Category.id_comp, whiskerLeft_comp, Category.assoc]

/-- In the precomposed groupoid, composing the inverse of an arrow after it gives the identity at its source. -/
private theorem restrict_comp_inverse {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    ∀ {W : C' ⥤ Type w} (a : W ⟶ (ι ⋙ G.R))
      (h : (a ≫ (whiskerLeft ι G.i)) ≫ (whiskerLeft ι G.s) = a ≫ (whiskerLeft ι G.t)),
      pullback.lift (a ≫ (whiskerLeft ι G.i)) a h ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) = (a ≫ (whiskerLeft ι G.s)) ≫ (whiskerLeft ι G.e) := by
  intro W a h
  have h₀ : (𝟙 G.R ≫ G.i) ≫ G.s = 𝟙 G.R ≫ G.t := by
    simp [G.inverse_source]
  calc
    _ = a ≫ whiskerLeft ι
        (pullback.lift (𝟙 G.R ≫ G.i) (𝟙 G.R) h₀ ≫ G.c) := by
      simpa only [Category.id_comp, whiskerLeft_id', Category.comp_id] using
        (restrict_lift_comp ι G.s G.t G.c a (𝟙 G.R ≫ G.i) (𝟙 G.R) h₀
          (by simpa only [Category.id_comp, whiskerLeft_id', Category.comp_id] using h))
    _ = _ := by
      rw [G.comp_inverse (𝟙 G.R) h₀, Category.id_comp, whiskerLeft_comp, Category.assoc]

/-- Restriction of a groupoid in functors along `ι : C' ⥤ C`. When `C'` is a subcategory of
`C`, take `ι` to be `ObjectProperty.ι` or `wideSubcategoryInclusion W ⋙ P.ι`. -/
def restrict {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    GroupoidInFunctors.{u', v', w} C' where
  U := ι ⋙ G.U
  R := ι ⋙ G.R
  s := whiskerLeft ι G.s
  t := whiskerLeft ι G.t
  c := (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
      whiskerLeft ι G.c
  e := whiskerLeft ι G.e
  i := whiskerLeft ι G.i
  comp_source := private restrict_comp_source G ι
  comp_target := private restrict_comp_target G ι
  identity_source := private restrict_identity_source G ι
  identity_target := private restrict_identity_target G ι
  inverse_source := private restrict_inverse_source G ι
  inverse_target := private restrict_inverse_target G ι
  associativity := private restrict_associativity G ι
  right_identity := private restrict_right_identity G ι
  left_identity := private restrict_left_identity G ι
  inverse_comp := private restrict_inverse_comp G ι
  comp_inverse := private restrict_comp_inverse G ι

/-- Restriction of the object functor is precomposition with `ι`. -/
theorem restrict_U {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).U = ι ⋙ G.U := rfl

/-- Restriction of the arrow functor is precomposition with `ι`. -/
theorem restrict_R {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).R = ι ⋙ G.R := rfl

/-- Restriction of the source transformation is left whiskering by `ι`. -/
theorem restrict_s {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).s = whiskerLeft ι G.s := rfl

/-- Restriction of the target transformation is left whiskering by `ι`. -/
theorem restrict_t {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).t = whiskerLeft ι G.t := rfl

/-- Restriction of composition is left whiskering, transported by the pullback-preservation
isomorphism of `(whiskeringLeft C' C (Type w)).obj ι`. -/
theorem restrict_c {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).c =
      (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c := rfl

/-- Restriction of the identity-arrow map is left whiskering by `ι`. -/
theorem restrict_e {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).e = whiskerLeft ι G.e := rfl

/-- Restriction of the inverse-arrow map is left whiskering by `ι`. -/
theorem restrict_i {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).i = whiskerLeft ι G.i := rfl

/-- Restriction precomposes the object and arrow functors, left-whiskers the source, target,
identity, and inverse maps, and transports composition through the pullback comparison. -/
theorem restrict_spec {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).U = ι ⋙ G.U ∧
      (G.restrict ι).R = ι ⋙ G.R ∧
      (G.restrict ι).s = whiskerLeft ι G.s ∧
      (G.restrict ι).t = whiskerLeft ι G.t ∧
      (G.restrict ι).c =
        (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
          whiskerLeft ι G.c ∧
      (G.restrict ι).e = whiskerLeft ι G.e ∧
      (G.restrict ι).i = whiskerLeft ι G.i :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Restriction along the identity functor recovers the original groupoid in functors. -/
theorem restrict_id (G : GroupoidInFunctors.{u, v, w} C) : G.restrict (𝟭 C) = G := by
  have hh : (PreservesPullback.iso ((whiskeringLeft C C (Type w)).obj (𝟭 C))
      G.s G.t).hom = 𝟙 (pullback G.s G.t) := by
    apply pullback.hom_ext
    · simp
      rfl
    · simp
      rfl
  have hi : (PreservesPullback.iso ((whiskeringLeft C C (Type w)).obj (𝟭 C))
      G.s G.t).inv = 𝟙 (pullback G.s G.t) := by
    apply (cancel_mono (PreservesPullback.iso
      ((whiskeringLeft C C (Type w)).obj (𝟭 C)) G.s G.t).hom).1
    rw [Iso.inv_hom_id, hh]
    rfl
  cases G
  simp only [restrict, hi, Category.id_comp]
  rfl

/-- Restriction along a composite functor is the composite of restrictions. -/
theorem restrict_comp {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    {C'' : Type u''} [Category.{v''} C''] [HasPullbacks (C'' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) (ι' : C'' ⥤ C') :
    G.restrict (ι' ⋙ ι) = (G.restrict ι).restrict ι' := by
  let F := (whiskeringLeft C' C (Type w)).obj ι
  let F' := (whiskeringLeft C'' C' (Type w)).obj ι'
  let e := PreservesPullback.iso F G.s G.t
  let e' := PreservesPullback.iso F' (F.map G.s) (F.map G.t)
  have hi : (PreservesPullback.iso
      ((whiskeringLeft C'' C (Type w)).obj (ι' ⋙ ι)) G.s G.t).inv =
        e'.inv ≫ F'.map e.inv := by
    apply (Iso.inv_eq_inv _ (F'.mapIso e ≪≫ e')).2
    change pullbackComparison (F ⋙ F') G.s G.t =
      F'.map (pullbackComparison F G.s G.t) ≫
        pullbackComparison F' (F.map G.s) (F.map G.t)
    exact pullbackComparison_comp F F' G.s G.t
  cases G
  simp only [restrict, hi, F, F', e, e', whiskerLeft_comp, Category.assoc]
  rfl

end CategoryTheory.GroupoidInFunctors
