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

variable {C : Type u} [Category.{v} C] [HasPullbacks (C ⥤ Type w)]

/-- The source of a restricted composite is the source of its earlier arrow. -/
private theorem restrict_comp_source {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) ≫ (whiskerLeft ι G.s) =
      pullback.snd (whiskerLeft ι G.s) (whiskerLeft ι G.t) ≫ whiskerLeft ι G.s := sorry

/-- The target of a restricted composite is the target of its later arrow. -/
private theorem restrict_comp_target {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) ≫ (whiskerLeft ι G.t) =
      pullback.fst (whiskerLeft ι G.s) (whiskerLeft ι G.t) ≫ whiskerLeft ι G.t := sorry

/-- In the precomposed groupoid, identity arrows have the specified source. -/
private theorem restrict_identity_source {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (whiskerLeft ι G.e) ≫ (whiskerLeft ι G.s) = 𝟙 (ι ⋙ G.U) := sorry

/-- In the precomposed groupoid, identity arrows have the specified target. -/
private theorem restrict_identity_target {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (whiskerLeft ι G.e) ≫ (whiskerLeft ι G.t) = 𝟙 (ι ⋙ G.U) := sorry

/-- In the precomposed groupoid, inversion exchanges source with target. -/
private theorem restrict_inverse_source {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (whiskerLeft ι G.i) ≫ (whiskerLeft ι G.s) = whiskerLeft ι G.t := sorry

/-- In the precomposed groupoid, inversion exchanges target with source. -/
private theorem restrict_inverse_target {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (whiskerLeft ι G.i) ≫ (whiskerLeft ι G.t) = whiskerLeft ι G.s := sorry

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
        whiskerLeft ι G.c) := sorry

/-- In the precomposed groupoid, composing an arrow with the identity at its source does not change it. -/
private theorem restrict_right_identity {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    ∀ {W : C' ⥤ Type w} (a : W ⟶ (ι ⋙ G.R))
      (h : a ≫ (whiskerLeft ι G.s) = ((a ≫ (whiskerLeft ι G.s)) ≫ (whiskerLeft ι G.e)) ≫ (whiskerLeft ι G.t)),
      pullback.lift a ((a ≫ (whiskerLeft ι G.s)) ≫ (whiskerLeft ι G.e)) h ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) = a := sorry

/-- In the precomposed groupoid, composing the identity at the target of an arrow with that arrow does not change it. -/
private theorem restrict_left_identity {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    ∀ {W : C' ⥤ Type w} (a : W ⟶ (ι ⋙ G.R))
      (h : ((a ≫ (whiskerLeft ι G.t)) ≫ (whiskerLeft ι G.e)) ≫ (whiskerLeft ι G.s) = a ≫ (whiskerLeft ι G.t)),
      pullback.lift ((a ≫ (whiskerLeft ι G.t)) ≫ (whiskerLeft ι G.e)) a h ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) = a := sorry

/-- In the precomposed groupoid, composing an arrow after its inverse gives the identity at its target. -/
private theorem restrict_inverse_comp {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    ∀ {W : C' ⥤ Type w} (a : W ⟶ (ι ⋙ G.R))
      (h : a ≫ (whiskerLeft ι G.s) = (a ≫ (whiskerLeft ι G.i)) ≫ (whiskerLeft ι G.t)),
      pullback.lift a (a ≫ (whiskerLeft ι G.i)) h ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) = (a ≫ (whiskerLeft ι G.t)) ≫ (whiskerLeft ι G.e) := sorry

/-- In the precomposed groupoid, composing the inverse of an arrow after it gives the identity at its source. -/
private theorem restrict_comp_inverse {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    ∀ {W : C' ⥤ Type w} (a : W ⟶ (ι ⋙ G.R))
      (h : (a ≫ (whiskerLeft ι G.i)) ≫ (whiskerLeft ι G.s) = a ≫ (whiskerLeft ι G.t)),
      pullback.lift (a ≫ (whiskerLeft ι G.i)) a h ≫ ((PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c) = (a ≫ (whiskerLeft ι G.s)) ≫ (whiskerLeft ι G.e) := sorry

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
    (G.restrict ι).U = ι ⋙ G.U := sorry

/-- Restriction of the arrow functor is precomposition with `ι`. -/
theorem restrict_R {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).R = ι ⋙ G.R := sorry

/-- Restriction of the source transformation is left whiskering by `ι`. -/
theorem restrict_s {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).s = whiskerLeft ι G.s := sorry

/-- Restriction of the target transformation is left whiskering by `ι`. -/
theorem restrict_t {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).t = whiskerLeft ι G.t := sorry

/-- Restriction of composition is left whiskering, transported by the pullback-preservation
isomorphism of `(whiskeringLeft C' C (Type w)).obj ι`. -/
theorem restrict_c {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).c =
      (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c := sorry

/-- Restriction of the identity-arrow map is left whiskering by `ι`. -/
theorem restrict_e {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).e = whiskerLeft ι G.e := sorry

/-- Restriction of the inverse-arrow map is left whiskering by `ι`. -/
theorem restrict_i {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).i = whiskerLeft ι G.i := sorry

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
      (G.restrict ι).i = whiskerLeft ι G.i := sorry

/-- Restriction along the identity functor recovers the original groupoid in functors. -/
theorem restrict_id (G : GroupoidInFunctors.{u, v, w} C) : G.restrict (𝟭 C) = G := sorry

/-- Restriction along a composite functor is the composite of restrictions. -/
theorem restrict_comp {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    {C'' : Type u''} [Category.{v''} C''] [HasPullbacks (C'' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) (ι' : C'' ⥤ C') :
    G.restrict (ι' ⋙ ι) = (G.restrict ι).restrict ι' := sorry

end CategoryTheory.GroupoidInFunctors
