/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation

/-!
# Groupoid schemes

This module bundles the object and arrow schemes of a groupoid scheme over a base, together
with their structure maps and pointwise groupoid laws.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A groupoid scheme over `S` consists of object and arrow schemes, structure maps, and
pointwise groupoid laws. In `pullback s t`, the first projection is the later arrow and the
second projection is the earlier arrow. -/
structure GroupoidScheme (S : Scheme.{u}) where
  /-- The scheme of objects over the base. -/
  U : Over S
  /-- The scheme of arrows over the base. -/
  R : Over S
  /-- The source map. -/
  s : R ⟶ U
  /-- The target map. -/
  t : R ⟶ U
  /-- Composition of composable arrows. -/
  c : pullback s t ⟶ R
  /-- The identity-arrow map. -/
  e : U ⟶ R
  /-- The inverse-arrow map. -/
  i : R ⟶ R
  /-- The source of a composite is the source of its earlier arrow. -/
  comp_source : c ≫ s = pullback.snd s t ≫ s
  /-- The target of a composite is the target of its later arrow. -/
  comp_target : c ≫ t = pullback.fst s t ≫ t
  /-- Identity arrows have the specified source. -/
  identity_source : e ≫ s = 𝟙 U
  /-- Identity arrows have the specified target. -/
  identity_target : e ≫ t = 𝟙 U
  /-- Inversion exchanges source with target. -/
  inverse_source : i ≫ s = t
  /-- Inversion exchanges target with source. -/
  inverse_target : i ≫ t = s
  /-- Composition is associative on every scheme of points over `S`. -/
  associativity :
    ∀ {T : Over S} (a b d : T ⟶ R)
      (h_ab : a ≫ s = b ≫ t) (h_bd : b ≫ s = d ≫ t)
      (h_ab_d : (pullback.lift a b h_ab ≫ c) ≫ s = d ≫ t)
      (h_a_bd : a ≫ s = (pullback.lift b d h_bd ≫ c) ≫ t),
      pullback.lift (pullback.lift a b h_ab ≫ c) d h_ab_d ≫ c =
        pullback.lift a (pullback.lift b d h_bd ≫ c) h_a_bd ≫ c
  /-- Composing an arrow with the identity at its source does not change it. -/
  right_identity :
    ∀ {T : Over S} (a : T ⟶ R)
      (h : a ≫ s = ((a ≫ s) ≫ e) ≫ t),
      pullback.lift a ((a ≫ s) ≫ e) h ≫ c = a
  /-- Composing the identity at the target of an arrow with that arrow does not change it. -/
  left_identity :
    ∀ {T : Over S} (a : T ⟶ R)
      (h : ((a ≫ t) ≫ e) ≫ s = a ≫ t),
      pullback.lift ((a ≫ t) ≫ e) a h ≫ c = a
  /-- Composing an arrow after its inverse gives the identity at its target. -/
  inverse_comp :
    ∀ {T : Over S} (a : T ⟶ R)
      (h : a ≫ s = (a ≫ i) ≫ t),
      pullback.lift a (a ≫ i) h ≫ c = (a ≫ t) ≫ e
  /-- Composing the inverse of an arrow after it gives the identity at its source. -/
  comp_inverse :
    ∀ {T : Over S} (a : T ⟶ R)
      (h : (a ≫ i) ≫ s = a ≫ t),
      pullback.lift (a ≫ i) a h ≫ c = (a ≫ s) ≫ e

namespace GroupoidScheme

/-- The discrete groupoid scheme on a scheme `U` over `S`. -/
def discrete {S : Scheme.{u}} (U : Over S) : GroupoidScheme S where
  U := U
  R := U
  s := 𝟙 U
  t := 𝟙 U
  c := pullback.fst (𝟙 U) (𝟙 U)
  e := 𝟙 U
  i := 𝟙 U
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object scheme of the discrete groupoid scheme is `U`. -/
theorem discrete_U {S : Scheme.{u}} (U : Over S) : (discrete U).U = U := sorry

/-- The arrow scheme of the discrete groupoid scheme is `U`. -/
theorem discrete_R {S : Scheme.{u}} (U : Over S) : (discrete U).R = U := sorry

/-- The source map of the discrete groupoid scheme is the identity. -/
theorem discrete_s {S : Scheme.{u}} (U : Over S) : (discrete U).s = 𝟙 U := sorry

/-- The target map of the discrete groupoid scheme is the identity. -/
theorem discrete_t {S : Scheme.{u}} (U : Over S) : (discrete U).t = 𝟙 U := sorry

/-- The composition map of the discrete groupoid scheme is the first pullback projection. -/
theorem discrete_c {S : Scheme.{u}} (U : Over S) :
    (discrete U).c = pullback.fst (𝟙 U) (𝟙 U) := sorry

/-- The identity map of the discrete groupoid scheme is the identity. -/
theorem discrete_e {S : Scheme.{u}} (U : Over S) : (discrete U).e = 𝟙 U := sorry

/-- The inverse map of the discrete groupoid scheme is the identity. -/
theorem discrete_i {S : Scheme.{u}} (U : Over S) : (discrete U).i = 𝟙 U := sorry

/-- Compose two `T`-valued arrows whose source and target agree. -/
def compose {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (a b : T ⟶ G.R) (h : a ≫ G.s = b ≫ G.t) : T ⟶ G.R :=
  pullback.lift a b h ≫ G.c

/-- The source of a pointwise composite is the source of its earlier arrow. -/
theorem compose_source {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (a b : T ⟶ G.R) (h : a ≫ G.s = b ≫ G.t) :
    G.compose a b h ≫ G.s = b ≫ G.s := sorry

/-- The target of a pointwise composite is the target of its later arrow. -/
theorem compose_target {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (a b : T ⟶ G.R) (h : a ≫ G.s = b ≫ G.t) :
    G.compose a b h ≫ G.t = a ≫ G.t := sorry

/-- Composing an arrow with the identity at its source leaves the arrow unchanged. -/
theorem compose_right_identity {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (a : T ⟶ G.R) (h : a ≫ G.s = ((a ≫ G.s) ≫ G.e) ≫ G.t) :
    G.compose a ((a ≫ G.s) ≫ G.e) h = a := sorry

/-- Composing the identity at an arrow's target with the arrow leaves it unchanged. -/
theorem compose_left_identity {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (a : T ⟶ G.R) (h : ((a ≫ G.t) ≫ G.e) ≫ G.s = a ≫ G.t) :
    G.compose ((a ≫ G.t) ≫ G.e) a h = a := sorry

/-- Pointwise composition of three composable arrows is associative. -/
theorem compose_assoc {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (a b d : T ⟶ G.R) (h_ab : a ≫ G.s = b ≫ G.t) (h_bd : b ≫ G.s = d ≫ G.t)
    (h_ab_d : G.compose a b h_ab ≫ G.s = d ≫ G.t)
    (h_a_bd : a ≫ G.s = G.compose b d h_bd ≫ G.t) :
    G.compose (G.compose a b h_ab) d h_ab_d =
      G.compose a (G.compose b d h_bd) h_a_bd := sorry

/-- Composing an arrow with its inverse gives the identity at its target. -/
theorem compose_inverse {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (a : T ⟶ G.R) (h : a ≫ G.s = (a ≫ G.i) ≫ G.t) :
    G.compose a (a ≫ G.i) h = (a ≫ G.t) ≫ G.e := sorry

/-- Composing the inverse of an arrow with the arrow gives the identity at its source. -/
theorem inverse_compose {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (a : T ⟶ G.R) (h : (a ≫ G.i) ≫ G.s = a ≫ G.t) :
    G.compose (a ≫ G.i) a h = (a ≫ G.s) ≫ G.e := sorry

/-- Forget a groupoid scheme to its underlying pre-relation, with defining map `(t, s)`. -/
def toPreRelation {S : Scheme.{u}} (G : GroupoidScheme S) : Scheme.PreRelation G.U :=
  Scheme.PreRelation.ofHom (prod.lift G.t G.s)

/-- The target projection of the underlying pre-relation is the target map. -/
theorem toPreRelation_t {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toPreRelation.t = G.t := sorry

/-- The source projection of the underlying pre-relation is the source map. -/
theorem toPreRelation_s {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toPreRelation.s = G.s := sorry

/-- A morphism between two `T`-valued objects of a groupoid scheme. -/
structure PointHom {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (x y : T ⟶ G.U) where
  /-- The underlying `T`-valued arrow. -/
  arrow : T ⟶ G.R
  /-- The arrow has source `x`. -/
  source : arrow ≫ G.s = x
  /-- The arrow has target `y`. -/
  target : arrow ≫ G.t = y

namespace PointHom

/-- Construct a pointwise morphism from an arrow with specified endpoints. -/
def ofArrow {S : Scheme.{u}} {G : GroupoidScheme S} {T : Over S}
    {x y : T ⟶ G.U} (arrow : T ⟶ G.R)
    (source : arrow ≫ G.s = x) (target : arrow ≫ G.t = y) : G.PointHom x y :=
  ⟨arrow, source, target⟩

/-- The underlying arrow of `ofArrow` is the supplied arrow. -/
theorem ofArrow_arrow {S : Scheme.{u}} {G : GroupoidScheme S} {T : Over S}
    {x y : T ⟶ G.U} (arrow : T ⟶ G.R)
    (source : arrow ≫ G.s = x) (target : arrow ≫ G.t = y) :
    (ofArrow arrow source target).arrow = arrow := rfl

/-- Pointwise morphisms with the same underlying arrow are equal. -/
theorem ext {S : Scheme.{u}} {G : GroupoidScheme S} {T : Over S}
    {x y : T ⟶ G.U} {f g : G.PointHom x y} (h : f.arrow = g.arrow) : f = g := by
  cases f with
  | mk f fs ft =>
    cases g with
    | mk g gs gt =>
      cases h
      rfl

end PointHom

/-- The explicit groupoid structure on the `T`-points of a groupoid scheme. -/
@[reducible]
def pointGroupoid {S : Scheme.{u}} (G : GroupoidScheme S) (T : Over S) :
    CategoryTheory.Groupoid (T ⟶ G.U) where
  Hom := fun x y ↦ G.PointHom x y
  id := fun x ↦
    { arrow := x ≫ G.e
      source := by simp [Category.assoc, G.identity_source]
      target := by simp [Category.assoc, G.identity_target] }
  comp := fun f g ↦
    { arrow := G.compose g.arrow f.arrow (g.source.trans f.target.symm)
      source := by
        simp [compose, Category.assoc, G.comp_source, pullback.lift_snd_assoc, f.source]
      target := by
        simp [compose, Category.assoc, G.comp_target, pullback.lift_fst_assoc, g.target] }
  id_comp := by
    intro x y f
    apply PointHom.ext
    change G.compose f.arrow (x ≫ G.e) _ = f.arrow
    have hri : f.arrow ≫ G.s = ((f.arrow ≫ G.s) ≫ G.e) ≫ G.t := by
      calc
        f.arrow ≫ G.s = x := f.source
        _ = (x ≫ G.e) ≫ G.t := by simp [Category.assoc, G.identity_target]
        _ = ((f.arrow ≫ G.s) ≫ G.e) ≫ G.t := by rw [f.source]
    simpa [compose, f.source] using G.right_identity f.arrow hri
  comp_id := by
    intro x y f
    apply PointHom.ext
    change G.compose (y ≫ G.e) f.arrow _ = f.arrow
    have hli : ((f.arrow ≫ G.t) ≫ G.e) ≫ G.s = f.arrow ≫ G.t := by
      calc
        ((f.arrow ≫ G.t) ≫ G.e) ≫ G.s = (y ≫ G.e) ≫ G.s := by rw [f.target]
        _ = y := by simp [Category.assoc, G.identity_source]
        _ = f.arrow ≫ G.t := f.target.symm
    simpa [compose, f.target] using G.left_identity f.arrow hli
  assoc := by
    intro w x y z f g h
    apply PointHom.ext
    let h_hg : h.arrow ≫ G.s = g.arrow ≫ G.t := h.source.trans g.target.symm
    let h_gf : g.arrow ≫ G.s = f.arrow ≫ G.t := g.source.trans f.target.symm
    let h_hg_f : G.compose h.arrow g.arrow h_hg ≫ G.s = f.arrow ≫ G.t := by
      simpa [compose, Category.assoc, G.comp_source, pullback.lift_snd_assoc] using h_gf
    let h_h_gf : h.arrow ≫ G.s = G.compose g.arrow f.arrow h_gf ≫ G.t := by
      simpa [compose, Category.assoc, G.comp_target, pullback.lift_fst_assoc] using h_hg
    simpa [compose] using
      (G.associativity h.arrow g.arrow f.arrow h_hg h_gf h_hg_f h_h_gf).symm
  inv := fun f ↦
    { arrow := f.arrow ≫ G.i
      source := by
        simp [Category.assoc, G.inverse_source, f.target]
      target := by
        simp [Category.assoc, G.inverse_target, f.source] }
  inv_comp := by
    intro x y f
    apply PointHom.ext
    change G.compose f.arrow (f.arrow ≫ G.i) _ = y ≫ G.e
    have hi : f.arrow ≫ G.s = (f.arrow ≫ G.i) ≫ G.t := by
      simp [Category.assoc, G.inverse_target]
    simpa [compose, f.target] using G.inverse_comp f.arrow hi
  comp_inv := by
    intro x y f
    apply PointHom.ext
    change G.compose (f.arrow ≫ G.i) f.arrow _ = x ≫ G.e
    have hi : (f.arrow ≫ G.i) ≫ G.s = f.arrow ≫ G.t := by
      simp [Category.assoc, G.inverse_source]
    simpa [compose, f.source] using G.comp_inverse f.arrow hi

/-- The bundled groupoid of `T`-points of a groupoid scheme. -/
def groupoidPoints {S : Scheme.{u}} (G : GroupoidScheme S) (T : Over S) : Grpd.{u, u} :=
  ⟨T ⟶ G.U, pointGroupoid G T⟩

/-- The objects of `groupoidPoints G T` are the morphisms `T ⟶ G.U`. -/
theorem groupoidPoints_obj {S : Scheme.{u}} (G : GroupoidScheme S) (T : Over S) :
    (G.groupoidPoints T : Type u) = (T ⟶ G.U) := sorry

/-- The bundled point groupoid carries the explicitly defined groupoid structure. -/
theorem groupoidPoints_str {S : Scheme.{u}} (G : GroupoidScheme S) (T : Over S) :
    (G.groupoidPoints T).str = G.pointGroupoid T := sorry

/-- The underlying arrow of an identity in the point groupoid is induced by `G.e`. -/
theorem groupoidPoints_id_arrow {S : Scheme.{u}} (G : GroupoidScheme S) (T : Over S)
    (x : G.groupoidPoints T) :
    ((𝟙 x : x ⟶ x)).arrow = x ≫ G.e := sorry

/-- The underlying arrow of a composite in the point groupoid is given by `G.compose`. -/
theorem groupoidPoints_comp_arrow {S : Scheme.{u}} (G : GroupoidScheme S) (T : Over S)
    {x y z : G.groupoidPoints T} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).arrow =
      G.compose g.arrow f.arrow (g.source.trans f.target.symm) := sorry

/-- The underlying arrow of an inverse in the point groupoid is induced by `G.i`. -/
theorem groupoidPoints_inv_arrow {S : Scheme.{u}} (G : GroupoidScheme S) (T : Over S)
    {x y : G.groupoidPoints T} (f : x ⟶ y) :
    (CategoryTheory.Groupoid.inv f).arrow = f.arrow ≫ G.i := sorry

/-- The functor of points of a groupoid scheme, valued in bundled groupoids. -/
def points {S : Scheme.{u}} (G : GroupoidScheme S) : (Over S)ᵒᵖ ⥤ Grpd.{u, u} where
  obj T := G.groupoidPoints T.unop
  map f :=
    { obj := fun x ↦ f.unop ≫ x
      map := fun p ↦
        { arrow := f.unop ≫ p.arrow
          source := sorry
          target := sorry }
      map_id := sorry
      map_comp := sorry }
  map_id := sorry
  map_comp := sorry

/-- The objects of the point groupoid over `T` are the morphisms `T ⟶ G.U`. -/
theorem points_obj {S : Scheme.{u}} (G : GroupoidScheme S) (T : Over S) :
    (G.points.obj (Opposite.op T) : Type u) = (T ⟶ G.U) := sorry

/-- Pullback of points along a morphism is given by precomposition. -/
theorem points_map_obj {S : Scheme.{u}} (G : GroupoidScheme S) {T T' : (Over S)ᵒᵖ}
    (f : T ⟶ T') (x : T.unop ⟶ G.U) :
    (G.points.map f).obj x = f.unop ≫ x := sorry

/-- Pullback of a pointwise arrow along a base morphism is given by precomposition. -/
theorem points_map_arrow {S : Scheme.{u}} (G : GroupoidScheme S) {T T' : (Over S)ᵒᵖ}
    (f : T ⟶ T') {x y : T.unop ⟶ G.U} (p : G.PointHom x y) :
    ((G.points.map f).map p).arrow = f.unop ≫ p.arrow := sorry

/-- The canonical map between composable-arrow pullbacks induced by maps of objects and arrows. -/
def composableMap {S : Scheme.{u}} {G H : GroupoidScheme S}
    (obj : G.U ⟶ H.U) (arrow : G.R ⟶ H.R)
    (map_s : G.s ≫ obj = arrow ≫ H.s) (map_t : G.t ≫ obj = arrow ≫ H.t) :
    pullback G.s G.t ⟶ pullback H.s H.t :=
  pullback.map G.s G.t H.s H.t arrow arrow obj map_s map_t

/-- The first projection of `composableMap` is the arrow map after the first projection. -/
theorem composableMap_fst {S : Scheme.{u}} {G H : GroupoidScheme S}
    (obj : G.U ⟶ H.U) (arrow : G.R ⟶ H.R)
    (map_s : G.s ≫ obj = arrow ≫ H.s) (map_t : G.t ≫ obj = arrow ≫ H.t) :
    composableMap obj arrow map_s map_t ≫ pullback.fst H.s H.t =
      pullback.fst G.s G.t ≫ arrow := sorry

/-- The second projection of `composableMap` is the arrow map after the second projection. -/
theorem composableMap_snd {S : Scheme.{u}} {G H : GroupoidScheme S}
    (obj : G.U ⟶ H.U) (arrow : G.R ⟶ H.R)
    (map_s : G.s ≫ obj = arrow ≫ H.s) (map_t : G.t ≫ obj = arrow ≫ H.t) :
    composableMap obj arrow map_s map_t ≫ pullback.snd H.s H.t =
      pullback.snd G.s G.t ≫ arrow := sorry

/-- A morphism of groupoid schemes consists of compatible maps on objects and arrows. -/
structure Hom {S : Scheme.{u}} (G H : GroupoidScheme S) where
  /-- The map on objects. -/
  obj : G.U ⟶ H.U
  /-- The map on arrows. -/
  arrow : G.R ⟶ H.R
  /-- Compatibility with source. -/
  map_s : G.s ≫ obj = arrow ≫ H.s
  /-- Compatibility with target. -/
  map_t : G.t ≫ obj = arrow ≫ H.t
  /-- Compatibility with composition. -/
  map_c : G.c ≫ arrow = composableMap obj arrow map_s map_t ≫ H.c

namespace Hom

/-- The identity morphism of a groupoid scheme. -/
def id {S : Scheme.{u}} (G : GroupoidScheme S) : Hom G G where
  obj := 𝟙 G.U
  arrow := 𝟙 G.R
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of the identity morphism is the identity. -/
theorem id_obj {S : Scheme.{u}} (G : GroupoidScheme S) : (id G).obj = 𝟙 G.U := sorry

/-- The arrow component of the identity morphism is the identity. -/
theorem id_arrow {S : Scheme.{u}} (G : GroupoidScheme S) : (id G).arrow = 𝟙 G.R := sorry

/-- Composition of morphisms of groupoid schemes. -/
def comp {S : Scheme.{u}} {G H K : GroupoidScheme S} (f : Hom G H) (g : Hom H K) :
    Hom G K where
  obj := f.obj ≫ g.obj
  arrow := f.arrow ≫ g.arrow
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of a composite is the composite of the object components. -/
theorem comp_obj {S : Scheme.{u}} {G H K : GroupoidScheme S}
    (f : Hom G H) (g : Hom H K) : (comp f g).obj = f.obj ≫ g.obj := sorry

/-- The arrow component of a composite is the composite of the arrow components. -/
theorem comp_arrow {S : Scheme.{u}} {G H K : GroupoidScheme S}
    (f : Hom G H) (g : Hom H K) : (comp f g).arrow = f.arrow ≫ g.arrow := sorry

/-- A groupoid-scheme morphism preserves identity arrows. -/
theorem map_e {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    G.e ≫ f.arrow = f.obj ≫ H.e := sorry

/-- A groupoid-scheme morphism preserves inverse arrows. -/
theorem map_i {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    G.i ≫ f.arrow = f.arrow ≫ H.i := sorry

/-- The induced map on pullbacks of the source and target maps. -/
def composableMap {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    pullback G.s G.t ⟶ pullback H.s H.t :=
  GroupoidScheme.composableMap f.obj f.arrow f.map_s f.map_t

/-- The first projection of `f.composableMap` is the arrow map after the first projection. -/
theorem composableMap_fst {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    f.composableMap ≫ pullback.fst H.s H.t = pullback.fst G.s G.t ≫ f.arrow :=
  GroupoidScheme.composableMap_fst f.obj f.arrow f.map_s f.map_t

/-- The second projection of `f.composableMap` is the arrow map after the second projection. -/
theorem composableMap_snd {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    f.composableMap ≫ pullback.snd H.s H.t = pullback.snd G.s G.t ≫ f.arrow :=
  GroupoidScheme.composableMap_snd f.obj f.arrow f.map_s f.map_t

/-- The natural transformation on point groupoids induced by a groupoid-scheme morphism. -/
def mapPoints {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    G.points ⟶ H.points where
  app T :=
    { obj := fun x ↦ x ≫ f.obj
      map := fun p ↦
        { arrow := p.arrow ≫ f.arrow
          source := sorry
          target := sorry }
      map_id := sorry
      map_comp := sorry }
  naturality := sorry

/-- On objects, the induced functor on points is postcomposition with the object map. -/
theorem mapPoints_app_obj {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H)
    (T : (Over S)ᵒᵖ) (x : T.unop ⟶ G.U) :
    (f.mapPoints.app T).obj x = x ≫ f.obj := sorry

/-- On arrows, the induced functor on points is postcomposition with the arrow map. -/
theorem mapPoints_app_map_arrow {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H)
    (T : (Over S)ᵒᵖ) {x y : T.unop ⟶ G.U} (p : G.PointHom x y) :
    ((f.mapPoints.app T).map p).arrow = p.arrow ≫ f.arrow := sorry

end Hom

end GroupoidScheme

end AlgebraicGeometry
