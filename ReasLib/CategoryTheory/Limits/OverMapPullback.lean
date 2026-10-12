/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

-- Import decisions:
-- * The Mathlib imports are public because `Over.map`, `Limits.pullback`, and
--   `CategoricalPullback` occur in exported types and transparent data bodies; categorical
--   pullback notation and projections come directly from `Categorical.Basic`.
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

@[expose] public section

/-!
# Categorical pullbacks of slice-map functors

This module identifies the categorical pullback of two functors induced by maps of slice
categories with the slice over the corresponding ordinary pullback.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section OverMapPullback

variable [Limits.HasPullbacks C]

namespace OverMapPullback

section ExplicitEquivalence

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Compatibility needed to lift the two legs of a categorical-pullback object to the ordinary
pullback of their base arrows. -/
private theorem objectCondition {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (x : (Over.map f) ⊡ (Over.map a)) :
    x.fst.hom ≫ f = (x.iso.hom.left ≫ x.snd.hom) ≫ a := sorry
/- Proof strategy: take the underlying-arrow equation of `Over.w x.iso.hom`, reverse it, and
reassociate. -/

/-- The arrow to the ordinary pullback carried by an object of
`(Over.map f) ⊡ (Over.map a)`. -/
private noncomputable def objectHom {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (x : (Over.map f) ⊡ (Over.map a)) : x.fst.left ⟶ Limits.pullback f a :=
  Limits.pullback.lift x.fst.hom (x.iso.hom.left ≫ x.snd.hom)
    (objectCondition f a x)

/-- Compatibility of `objectHom` with a morphism in the categorical pullback. -/
private theorem mapComm {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {x y : (Over.map f) ⊡ (Over.map a)} (φ : x ⟶ y) :
    φ.fst.left ≫ objectHom f a y = objectHom f a x := sorry
/- Proof strategy: use `Limits.pullback.hom_ext`; the first projection is `Over.w φ.fst`, and the
second combines the underlying equation of `φ.w` with `Over.w φ.snd`. -/

/-- The morphism over the ordinary pullback induced by a morphism in the categorical pullback. -/
private noncomputable def map {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {x y : (Over.map f) ⊡ (Over.map a)} (φ : x ⟶ y) :
    Over.mk (objectHom f a x) ⟶ Over.mk (objectHom f a y) :=
  Over.homMk φ.fst.left (mapComm f a φ)

/-- `map` preserves identity morphisms. -/
private theorem mapId {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (x : (Over.map f) ⊡ (Over.map a)) :
    map f a (𝟙 x) = 𝟙 (Over.mk (objectHom f a x)) := sorry
/- Proof strategy: apply `Over.OverMorphism.ext` and reduce to the identity law in `C`. -/

/-- `map` preserves composition. -/
private theorem mapComp {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {x y z : (Over.map f) ⊡ (Over.map a)} (φ : x ⟶ y) (ψ : y ⟶ z) :
    map f a (φ ≫ ψ) = map f a φ ≫ map f a ψ := sorry
/- Proof strategy: apply `Over.OverMorphism.ext` and reduce to associativity of underlying
morphisms. -/

/-- The forward map from the categorical pullback of slice postcomposition functors to the slice
over the ordinary pullback. -/
private noncomputable def forward {A W U : C} (f : W ⟶ U) (a : A ⟶ U) :
    (Over.map f) ⊡ (Over.map a) ⥤ Over (Limits.pullback f a) where
  obj x := Over.mk (objectHom f a x)
  map φ := map f a φ
  map_id := mapId f a
  map_comp := mapComp f a

/-- Coherence for the structural slice isomorphism in the inverse construction. -/
private theorem inverseObjectIsoComm {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (c : Over (Limits.pullback f a)) :
    (Iso.refl c.left).hom ≫
        ((Over.map a).obj (Over.mk (c.hom ≫ Limits.pullback.snd f a))).hom =
      ((Over.map f).obj (Over.mk (c.hom ≫ Limits.pullback.fst f a))).hom := sorry
/- Proof strategy: use `Limits.pullback.condition` and reassociate after the identity morphism. -/

/-- The structural isomorphism over `U` in the inverse construction. -/
private noncomputable def inverseObjectIso {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (c : Over (Limits.pullback f a)) :
    (Over.map f).obj (Over.mk (c.hom ≫ Limits.pullback.fst f a)) ≅
      (Over.map a).obj (Over.mk (c.hom ≫ Limits.pullback.snd f a)) :=
  Over.isoMk (Iso.refl c.left) (inverseObjectIsoComm f a c)

/-- The categorical-pullback object underlying an object of the slice over the ordinary
pullback. -/
private noncomputable def inverseObject {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (c : Over (Limits.pullback f a)) : (Over.map f) ⊡ (Over.map a) where
  fst := Over.mk (c.hom ≫ Limits.pullback.fst f a)
  snd := Over.mk (c.hom ≫ Limits.pullback.snd f a)
  iso := inverseObjectIso f a c

/-- Compatibility of the first inverse leg with a slice morphism. -/
private theorem inverseMapFstComm {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {c d : Over (Limits.pullback f a)} (g : c ⟶ d) :
    g.left ≫ (Over.mk (d.hom ≫ Limits.pullback.fst f a)).hom =
      (Over.mk (c.hom ≫ Limits.pullback.fst f a)).hom := sorry
/- Proof strategy: postcompose `Over.w g` with `Limits.pullback.fst f a` and reassociate. -/

/-- The first slice morphism in the inverse construction. -/
private noncomputable def inverseMapFst {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {c d : Over (Limits.pullback f a)} (g : c ⟶ d) :
    (inverseObject f a c).fst ⟶ (inverseObject f a d).fst :=
  Over.homMk g.left (inverseMapFstComm f a g)

/-- Compatibility of the second inverse leg with a slice morphism. -/
private theorem inverseMapSndComm {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {c d : Over (Limits.pullback f a)} (g : c ⟶ d) :
    g.left ≫ (Over.mk (d.hom ≫ Limits.pullback.snd f a)).hom =
      (Over.mk (c.hom ≫ Limits.pullback.snd f a)).hom := sorry
/- Proof strategy: postcompose `Over.w g` with `Limits.pullback.snd f a` and reassociate. -/

/-- The second slice morphism in the inverse construction. -/
private noncomputable def inverseMapSnd {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {c d : Over (Limits.pullback f a)} (g : c ⟶ d) :
    (inverseObject f a c).snd ⟶ (inverseObject f a d).snd :=
  Over.homMk g.left (inverseMapSndComm f a g)

/-- Compatibility of the two inverse legs with their structural isomorphisms. -/
private theorem inverseMapComm {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {c d : Over (Limits.pullback f a)} (g : c ⟶ d) :
    (Over.map f).map (inverseMapFst f a g) ≫ (inverseObject f a d).iso.hom =
      (inverseObject f a c).iso.hom ≫ (Over.map a).map (inverseMapSnd f a g) := sorry
/- Proof strategy: apply `Over.OverMorphism.ext`; all four underlying arrows are `g.left` and the
remaining equation is an identity law. -/

/-- The categorical-pullback morphism induced by a morphism over the ordinary pullback. -/
private noncomputable def inverseMap {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {c d : Over (Limits.pullback f a)} (g : c ⟶ d) :
    inverseObject f a c ⟶ inverseObject f a d where
  fst := inverseMapFst f a g
  snd := inverseMapSnd f a g
  w := inverseMapComm f a g

/-- `inverseMap` preserves identity morphisms. -/
private theorem inverseMapId {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (c : Over (Limits.pullback f a)) :
    inverseMap f a (𝟙 c) = 𝟙 (inverseObject f a c) := sorry
/- Proof strategy: apply `CategoricalPullback.hom_ext` and then `Over.OverMorphism.ext` on both
projections. -/

/-- `inverseMap` preserves composition. -/
private theorem inverseMapComp {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {c d e : Over (Limits.pullback f a)} (g : c ⟶ d) (h : d ⟶ e) :
    inverseMap f a (g ≫ h) = inverseMap f a g ≫ inverseMap f a h := sorry
/- Proof strategy: apply `CategoricalPullback.hom_ext` and then `Over.OverMorphism.ext` on both
projections. -/

/-- The inverse map from the slice over the ordinary pullback to the categorical pullback of
slice-postcomposition functors. -/
private noncomputable def inverse {A W U : C} (f : W ⟶ U) (a : A ⟶ U) :
    Over (Limits.pullback f a) ⥤ (Over.map f) ⊡ (Over.map a) where
  obj c := inverseObject f a c
  map g := inverseMap f a g
  map_id := inverseMapId f a
  map_comp := inverseMapComp f a

/-- Coherence of the first slice isomorphism in the unit component. -/
private theorem unitFstIsoComm {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (x : (Over.map f) ⊡ (Over.map a)) :
    (Iso.refl x.fst.left).hom ≫ ((forward f a ⋙ inverse f a).obj x).fst.hom =
      x.fst.hom := sorry
/- Proof strategy: project `objectHom` to the first pullback leg and use
`Limits.pullback.lift_fst`. -/

/-- The first slice isomorphism in the unit component. -/
private noncomputable def unitFstIso {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (x : (Over.map f) ⊡ (Over.map a)) :
    x.fst ≅ ((forward f a ⋙ inverse f a).obj x).fst :=
  Over.isoMk (Iso.refl x.fst.left) (unitFstIsoComm f a x)

/-- Coherence of the second slice isomorphism in the unit component. -/
private theorem unitSndIsoComm {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (x : (Over.map f) ⊡ (Over.map a)) :
    ((Over.forget U).mapIso x.iso.symm).hom ≫
        ((forward f a ⋙ inverse f a).obj x).snd.hom =
      x.snd.hom := sorry
/- Proof strategy: project `objectHom` to the second pullback leg, then cancel the underlying
components of `x.iso.symm` and `x.iso`. -/

/-- The second slice isomorphism in the unit component. -/
private noncomputable def unitSndIso {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (x : (Over.map f) ⊡ (Over.map a)) :
    x.snd ≅ ((forward f a ⋙ inverse f a).obj x).snd :=
  Over.isoMk ((Over.forget U).mapIso x.iso.symm) (unitSndIsoComm f a x)

/-- Compatibility of the two slice isomorphisms in the unit component. -/
private theorem unitComponentComm {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (x : (Over.map f) ⊡ (Over.map a)) :
    (Over.map f).map (unitFstIso f a x).hom ≫
        ((forward f a ⋙ inverse f a).obj x).iso.hom =
      x.iso.hom ≫ (Over.map a).map (unitSndIso f a x).hom := sorry
/- Proof strategy: apply `Over.OverMorphism.ext` and use `x.iso.hom_inv_id` on underlying
arrows. -/

/-- Objectwise unit of the ordinary-pullback comparison. -/
private noncomputable def unitComponent {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (x : (Over.map f) ⊡ (Over.map a)) :
    x ≅ (forward f a ⋙ inverse f a).obj x :=
  CategoricalPullback.mkIso (unitFstIso f a x) (unitSndIso f a x)
    (unitComponentComm f a x)

/-- Naturality of the ordinary-pullback comparison unit. -/
private theorem unitNaturality {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {x y : (Over.map f) ⊡ (Over.map a)} (φ : x ⟶ y) :
    φ ≫ (unitComponent f a y).hom =
      (unitComponent f a x).hom ≫ (forward f a ⋙ inverse f a).map φ := sorry
/- Proof strategy: apply `CategoricalPullback.hom_ext` and `Over.OverMorphism.ext`; the second
component is the underlying inverse-direction square `φ.w'`. -/

/-- Unit natural isomorphism of the ordinary-pullback comparison. -/
private noncomputable def unitIso {A W U : C} (f : W ⟶ U) (a : A ⟶ U) :
    𝟭 ((Over.map f) ⊡ (Over.map a)) ≅ forward f a ⋙ inverse f a :=
  NatIso.ofComponents (unitComponent f a) (unitNaturality f a)

/-- Coherence of the counit component over the ordinary pullback. -/
private theorem counitComponentComm {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (c : Over (Limits.pullback f a)) :
    (Iso.refl c.left).hom ≫ c.hom = ((inverse f a ⋙ forward f a).obj c).hom := sorry
/- Proof strategy: apply `Limits.pullback.hom_ext` and use the two lift projection equations. -/

/-- Objectwise counit of the ordinary-pullback comparison. -/
private noncomputable def counitComponent {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (c : Over (Limits.pullback f a)) :
    (inverse f a ⋙ forward f a).obj c ≅ c :=
  Over.isoMk (Iso.refl c.left) (counitComponentComm f a c)

/-- Naturality of the ordinary-pullback comparison counit. -/
private theorem counitNaturality {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {c d : Over (Limits.pullback f a)} (g : c ⟶ d) :
    (inverse f a ⋙ forward f a).map g ≫ (counitComponent f a d).hom =
      (counitComponent f a c).hom ≫ g := sorry
/- Proof strategy: apply `Over.OverMorphism.ext`; both sides have underlying arrow `g.left`. -/

/-- Counit natural isomorphism of the ordinary-pullback comparison. -/
private noncomputable def counitIso {A W U : C} (f : W ⟶ U) (a : A ⟶ U) :
    inverse f a ⋙ forward f a ≅ 𝟭 (Over (Limits.pullback f a)) :=
  NatIso.ofComponents (counitComponent f a) (counitNaturality f a)

/-- Triangle coherence for the ordinary-pullback comparison. -/
private theorem triangle {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (x : (Over.map f) ⊡ (Over.map a)) :
    (forward f a).map ((unitIso f a).hom.app x) ≫
        (counitIso f a).hom.app ((forward f a).obj x) =
      𝟙 ((forward f a).obj x) := sorry
/- Proof strategy: apply `Over.OverMorphism.ext`; the underlying arrow is the identity after the
two pullback projections. -/

end Implementation

/-- The canonical equivalence between the categorical pullback of slice-postcomposition functors
and the slice over the ordinary pullback of their base arrows. -/
noncomputable def equivalence {A W U : C} (f : W ⟶ U) (a : A ⟶ U) :
    (Over.map f) ⊡ (Over.map a) ≌ Over (Limits.pullback f a) where
  functor := Implementation.forward f a
  inverse := Implementation.inverse f a
  unitIso := Implementation.unitIso f a
  counitIso := Implementation.counitIso f a
  functor_unitIso_comp := Implementation.triangle f a

/-- The arrow represented by the forward equivalence projects to the first leg of the
categorical-pullback object. -/
@[simp] theorem equivalenceFunctorObjHomFst {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (x : (Over.map f) ⊡ (Over.map a)) :
    ((equivalence f a).functor.obj x).hom ≫ Limits.pullback.fst f a = x.fst.hom := sorry
/- Proof strategy: unfold the public equivalence through its private forward functor and apply
`Limits.pullback.lift_fst` to the explicitly assembled pullback lift. -/

/-- The arrow represented by the forward equivalence projects to the second leg, after the
structural isomorphism identifying the two slice domains. -/
@[simp] theorem equivalenceFunctorObjHomSnd {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (x : (Over.map f) ⊡ (Over.map a)) :
    ((equivalence f a).functor.obj x).hom ≫ Limits.pullback.snd f a =
      x.iso.hom.left ≫ x.snd.hom := sorry
/- Proof strategy: unfold the public equivalence through its private forward functor and apply
`Limits.pullback.lift_snd` to the explicit pullback lift. -/

/-- On morphisms, the forward equivalence uses the underlying arrow of the first slice
component. -/
@[simp] theorem equivalenceFunctorMapLeft {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {x y : (Over.map f) ⊡ (Over.map a)} (φ : x ⟶ y) :
    ((equivalence f a).functor.map φ).left = φ.fst.left := sorry
/- Proof strategy: unfold the public equivalence and its private morphism assembly; the
underlying arrow supplied to `Over.homMk` is exactly `φ.fst.left`. -/

/-- The first slice object of the inverse equivalence is obtained by composing with the first
ordinary-pullback projection. -/
@[simp] theorem equivalenceInverseObjFst {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (c : Over (Limits.pullback f a)) :
    ((equivalence f a).inverse.obj c).fst =
      Over.mk (c.hom ≫ Limits.pullback.fst f a) := sorry
/- Proof strategy: unfold the public equivalence through its private inverse functor and read
the first object field of the categorical-pullback object. -/

/-- The second slice object of the inverse equivalence is obtained by composing with the second
ordinary-pullback projection. -/
@[simp] theorem equivalenceInverseObjSnd {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    (c : Over (Limits.pullback f a)) :
    ((equivalence f a).inverse.obj c).snd =
      Over.mk (c.hom ≫ Limits.pullback.snd f a) := sorry
/- Proof strategy: unfold the public equivalence through its private inverse functor and read
the second object field of the categorical-pullback object. -/

namespace Implementation

/-- Naturality of the identity components comparing the forward equivalence with the first
projection. -/
private theorem functorFstNaturality {A W U : C} (f : W ⟶ U) (a : A ⟶ U)
    {x y : (Over.map f) ⊡ (Over.map a)} (φ : x ⟶ y) :
    ((equivalence f a).functor ⋙ Over.forget (Limits.pullback f a)).map φ ≫
        (Iso.refl _).hom =
      (Iso.refl _).hom ≫
        (π₁ (Over.map f) (Over.map a) ⋙ Over.forget W).map φ := sorry
/- Proof strategy: unfold `forward`; both sides are the underlying arrow `φ.fst.left`. -/

end Implementation

/-- The forward equivalence preserves the first underlying-object projection. -/
noncomputable def functorFstIso {A W U : C} (f : W ⟶ U) (a : A ⟶ U) :
    (equivalence f a).functor ⋙ Over.forget (Limits.pullback f a) ≅
      π₁ (Over.map f) (Over.map a) ⋙ Over.forget W :=
  NatIso.ofComponents (fun _ => Iso.refl _) (Implementation.functorFstNaturality f a)

end ExplicitEquivalence

end OverMapPullback

end OverMapPullback

end CategoryTheory
