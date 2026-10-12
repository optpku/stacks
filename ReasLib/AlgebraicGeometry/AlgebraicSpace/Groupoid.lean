/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Groupoids in algebraic spaces

This module bundles the object and arrow algebraic spaces of a groupoid in algebraic
spaces over a base, together with their structure maps and pointwise groupoid laws.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]

/-- A groupoid in algebraic spaces over `B` consists of object and arrow algebraic spaces,
structure maps, and pointwise groupoid laws. In `pullback s t`, the first projection is the
later arrow and the second projection is the earlier arrow. -/
structure GroupoidAlgebraicSpace (B : AlgebraicSpace S) where
  /-- The algebraic space of objects over the base. -/
  U : Over B
  /-- The algebraic space of arrows over the base. -/
  R : Over B
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
  /-- Composition is associative on every object of points over `B`. -/
  associativity :
    ∀ {T : Over B} (a b d : T ⟶ R)
      (h_ab : a ≫ s = b ≫ t) (h_bd : b ≫ s = d ≫ t)
      (h_ab_d : (pullback.lift a b h_ab ≫ c) ≫ s = d ≫ t)
      (h_a_bd : a ≫ s = (pullback.lift b d h_bd ≫ c) ≫ t),
      pullback.lift (pullback.lift a b h_ab ≫ c) d h_ab_d ≫ c =
        pullback.lift a (pullback.lift b d h_bd ≫ c) h_a_bd ≫ c
  /-- Composing an arrow with the identity at its source does not change it. -/
  right_identity :
    ∀ {T : Over B} (a : T ⟶ R)
      (h : a ≫ s = ((a ≫ s) ≫ e) ≫ t),
      pullback.lift a ((a ≫ s) ≫ e) h ≫ c = a
  /-- Composing the identity at the target of an arrow with that arrow does not change it. -/
  left_identity :
    ∀ {T : Over B} (a : T ⟶ R)
      (h : ((a ≫ t) ≫ e) ≫ s = a ≫ t),
      pullback.lift ((a ≫ t) ≫ e) a h ≫ c = a
  /-- Composing an arrow after its inverse gives the identity at its target. -/
  inverse_comp :
    ∀ {T : Over B} (a : T ⟶ R)
      (h : a ≫ s = (a ≫ i) ≫ t),
      pullback.lift a (a ≫ i) h ≫ c = (a ≫ t) ≫ e
  /-- Composing the inverse of an arrow after it gives the identity at its source. -/
  comp_inverse :
    ∀ {T : Over B} (a : T ⟶ R)
      (h : (a ≫ i) ≫ s = a ≫ t),
      pullback.lift (a ≫ i) a h ≫ c = (a ≫ s) ≫ e

namespace GroupoidAlgebraicSpace

/-- The discrete groupoid in algebraic spaces on an algebraic space `U` over `B`. -/
def discrete {B : AlgebraicSpace S} (U : Over B) :
    GroupoidAlgebraicSpace B where
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

/-- The object space of the discrete groupoid is `U`. -/
theorem discrete_U {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).U = U := sorry

/-- The arrow space of the discrete groupoid is `U`. -/
theorem discrete_R {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).R = U := sorry

/-- The source map of the discrete groupoid is the identity. -/
theorem discrete_s {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).s = 𝟙 U := sorry

/-- The target map of the discrete groupoid is the identity. -/
theorem discrete_t {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).t = 𝟙 U := sorry

/-- The composition map of the discrete groupoid is the first pullback projection. -/
theorem discrete_c {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).c = pullback.fst (𝟙 U) (𝟙 U) := sorry

/-- The identity map of the discrete groupoid is the identity. -/
theorem discrete_e {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).e = 𝟙 U := sorry

/-- The inverse map of the discrete groupoid is the identity. -/
theorem discrete_i {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).i = 𝟙 U := sorry

/-- Compose two `T`-valued arrows whose source and target agree. -/
def compose {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over B} (a b : T ⟶ G.R) (h : a ≫ G.s = b ≫ G.t) : T ⟶ G.R :=
  pullback.lift a b h ≫ G.c

/-- The source of a pointwise composite is the source of its earlier arrow. -/
theorem compose_source {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over B} (a b : T ⟶ G.R)
    (h : a ≫ G.s = b ≫ G.t) :
    G.compose a b h ≫ G.s = b ≫ G.s := sorry

/-- The target of a pointwise composite is the target of its later arrow. -/
theorem compose_target {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over B} (a b : T ⟶ G.R)
    (h : a ≫ G.s = b ≫ G.t) :
    G.compose a b h ≫ G.t = a ≫ G.t := sorry

/-- A morphism between two scheme-valued objects of a groupoid in algebraic spaces. -/
structure PointHom {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B)
    (x y : Over.mk σ ⟶ G.U) where
  /-- The underlying scheme-valued arrow. -/
  arrow : Over.mk σ ⟶ G.R
  /-- The arrow has source `x`. -/
  source : arrow ≫ G.s = x
  /-- The arrow has target `y`. -/
  target : arrow ≫ G.t = y

namespace PointHom

/-- Construct a pointwise morphism from an arrow with specified endpoints. -/
def ofArrow {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B} {x y : Over.mk σ ⟶ G.U}
    (arrow : Over.mk σ ⟶ G.R) (source : arrow ≫ G.s = x)
    (target : arrow ≫ G.t = y) : G.PointHom σ x y :=
  ⟨arrow, source, target⟩

/-- The underlying arrow of `ofArrow` is the supplied arrow. -/
theorem ofArrow_arrow {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (arrow : Over.mk σ ⟶ G.R)
    (source : arrow ≫ G.s = x) (target : arrow ≫ G.t = y) :
    (ofArrow arrow source target).arrow = arrow := sorry

/-- The endpoint equations of a pointwise morphism constructed by `ofArrow`. -/
theorem ofArrow_spec {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (arrow : Over.mk σ ⟶ G.R)
    (source : arrow ≫ G.s = x) (target : arrow ≫ G.t = y) :
    (ofArrow arrow source target).arrow ≫ G.s = x ∧
      (ofArrow arrow source target).arrow ≫ G.t = y := sorry

/-- Pointwise morphisms with the same underlying arrow are equal. -/
theorem ext {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B} {x y : Over.mk σ ⟶ G.U}
    {f g : G.PointHom σ x y} (h : f.arrow = g.arrow) : f = g := sorry

/-- The identity pointwise morphism is induced by the identity-arrow map. -/
def id {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) (x : Over.mk σ ⟶ G.U) :
    G.PointHom σ x x where
  arrow := x ≫ G.e
  source := sorry
  target := sorry

/-- The composite of pointwise morphisms is induced by groupoid composition. -/
def comp {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y z : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) (g : G.PointHom σ y z) :
    G.PointHom σ x z where
  arrow := G.compose g.arrow f.arrow (g.source.trans f.target.symm)
  source := sorry
  target := sorry

/-- The inverse pointwise morphism is induced by the inverse-arrow map. -/
def inv {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) : G.PointHom σ y x where
  arrow := f.arrow ≫ G.i
  source := sorry
  target := sorry

end PointHom

/-- The explicit groupoid structure on the scheme-valued `T`-points of a groupoid in
algebraic spaces. -/
@[reducible]
def pointGroupoid {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    CategoryTheory.Groupoid (Over.mk σ ⟶ G.U) where
  Hom := fun x y ↦ G.PointHom σ x y
  id := fun x ↦ PointHom.id (G := G) σ x
  comp := fun f g ↦ PointHom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry
  inv := fun f ↦ PointHom.inv f
  inv_comp := sorry
  comp_inv := sorry

/-- The bundled groupoid of scheme-valued `T`-points of a groupoid in algebraic spaces. -/
def groupoidPoints {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) : Grpd.{u + 1, u + 1} :=
  ⟨Over.mk σ ⟶ G.U, G.pointGroupoid σ⟩

/-- The objects of `groupoidPoints G σ` are the morphisms `Over.mk σ ⟶ G.U`. -/
theorem groupoidPoints_obj {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    (G.groupoidPoints σ : Type (u + 1)) = (Over.mk σ ⟶ G.U) := sorry

/-- Scheme-valued `T`-points form a groupoid whose morphisms from `x` to `y` are arrows
`Over.mk σ ⟶ G.R` with source `x` and target `y`. -/
theorem pointGroupoid_spec {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B)
    (x y : Over.mk σ ⟶ G.U) :
    (G.pointGroupoid σ).Hom x y = G.PointHom σ x y := sorry

/-- The identity and composition arrows in the point groupoid are induced by `G.e` and `G.c`. -/
theorem pointGroupoid_id_comp {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y z : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) (g : G.PointHom σ y z) :
    ((G.pointGroupoid σ).id x).arrow = x ≫ G.e ∧
      ((G.pointGroupoid σ).comp f g).arrow = G.compose g.arrow f.arrow
        (g.source.trans f.target.symm) := sorry

/-- The inversion arrow in the point groupoid is postcomposition with `G.i`. -/
theorem pointGroupoid_inv_arrow {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) :
    ((G.pointGroupoid σ).inv f).arrow = f.arrow ≫ G.i := sorry

/-- The canonical map between composable-arrow pullbacks induced by maps of objects and arrows. -/
def composableMap {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (obj : G.U ⟶ H.U) (arrow : G.R ⟶ H.R)
    (map_s : G.s ≫ obj = arrow ≫ H.s) (map_t : G.t ≫ obj = arrow ≫ H.t) :
    pullback G.s G.t ⟶ pullback H.s H.t :=
  pullback.map G.s G.t H.s H.t arrow arrow obj map_s map_t

/-- The first projection of `composableMap` is the arrow map after the first projection. -/
theorem composableMap_fst {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (obj : G.U ⟶ H.U) (arrow : G.R ⟶ H.R)
    (map_s : G.s ≫ obj = arrow ≫ H.s) (map_t : G.t ≫ obj = arrow ≫ H.t) :
    composableMap obj arrow map_s map_t ≫ pullback.fst H.s H.t =
      pullback.fst G.s G.t ≫ arrow := sorry

/-- The second projection of `composableMap` is the arrow map after the second projection. -/
theorem composableMap_snd {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (obj : G.U ⟶ H.U) (arrow : G.R ⟶ H.R)
    (map_s : G.s ≫ obj = arrow ≫ H.s) (map_t : G.t ≫ obj = arrow ≫ H.t) :
    composableMap obj arrow map_s map_t ≫ pullback.snd H.s H.t =
      pullback.snd G.s G.t ≫ arrow := sorry

/-- A morphism of groupoids in algebraic spaces consists of compatible maps on objects and
arrows. -/
structure Hom {B : AlgebraicSpace S} (G H : GroupoidAlgebraicSpace B) where
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

/-- The identity morphism of a groupoid in algebraic spaces. -/
def id {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) : Hom G G where
  obj := 𝟙 G.U
  arrow := 𝟙 G.R
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of the identity morphism is the identity. -/
theorem id_obj {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (id G).obj = 𝟙 G.U := sorry

/-- The arrow component of the identity morphism is the identity. -/
theorem id_arrow {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (id G).arrow = 𝟙 G.R := sorry

/-- Composition of morphisms of groupoids in algebraic spaces. -/
def comp {B : AlgebraicSpace S} {G H K : GroupoidAlgebraicSpace B}
    (f : Hom G H) (g : Hom H K) : Hom G K where
  obj := f.obj ≫ g.obj
  arrow := f.arrow ≫ g.arrow
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of a composite is the composite of the object components. -/
theorem comp_obj {B : AlgebraicSpace S} {G H K : GroupoidAlgebraicSpace B}
    (f : Hom G H) (g : Hom H K) : (comp f g).obj = f.obj ≫ g.obj := sorry

/-- The arrow component of a composite is the composite of the arrow components. -/
theorem comp_arrow {B : AlgebraicSpace S} {G H K : GroupoidAlgebraicSpace B}
    (f : Hom G H) (g : Hom H K) : (comp f g).arrow = f.arrow ≫ g.arrow := sorry

/-- Morphisms of groupoids in algebraic spaces are determined by their object and arrow maps. -/
theorem ext {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    {f g : Hom G H} (h_obj : f.obj = g.obj) (h_arrow : f.arrow = g.arrow) : f = g := sorry

/-- A morphism of groupoids in algebraic spaces preserves identity arrows. -/
theorem map_e {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) : G.e ≫ f.arrow = f.obj ≫ H.e := sorry

/-- A morphism of groupoids in algebraic spaces preserves inverse arrows. -/
theorem map_i {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) : G.i ≫ f.arrow = f.arrow ≫ H.i := sorry

/-- The induced map on pullbacks of the source and target maps. -/
def composableMap {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) : pullback G.s G.t ⟶ pullback H.s H.t :=
  GroupoidAlgebraicSpace.composableMap f.obj f.arrow f.map_s f.map_t

/-- The first projection of `f.composableMap` is the arrow map after the first projection. -/
theorem composableMap_fst {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    f.composableMap ≫ pullback.fst H.s H.t = pullback.fst G.s G.t ≫ f.arrow := sorry

/-- The second projection of `f.composableMap` is the arrow map after the second projection. -/
theorem composableMap_snd {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    f.composableMap ≫ pullback.snd H.s H.t = pullback.snd G.s G.t ≫ f.arrow := sorry

/-- The functor of scheme-valued point groupoids induced by a morphism of groupoids in
algebraic spaces. -/
def mapPoints {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    G.groupoidPoints σ ⟶ H.groupoidPoints σ where
  obj := fun x ↦ x ≫ f.obj
  map := fun p ↦
    { arrow := p.arrow ≫ f.arrow
      source := sorry
      target := sorry }
  map_id := sorry
  map_comp := sorry

/-- On objects, the induced functor on points is postcomposition with the object map. -/
theorem mapPoints_obj {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) {T : Over S}
    (σ : AlgebraicSpace.ofOver T ⟶ B) (x : Over.mk σ ⟶ G.U) :
    (f.mapPoints σ).obj x = x ≫ f.obj := sorry

/-- On arrows, the induced functor on points is postcomposition with the arrow map. -/
theorem mapPoints_map_arrow {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) {T : Over S}
    (σ : AlgebraicSpace.ofOver T ⟶ B) {x y : Over.mk σ ⟶ G.U}
    (p : G.PointHom σ x y) :
    ((f.mapPoints σ).map p).arrow = p.arrow ≫ f.arrow := sorry

/-- The object and arrow components of the functor induced on point groupoids. -/
theorem mapPoints_spec {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) {T : Over S}
    (σ : AlgebraicSpace.ofOver T ⟶ B) (x : Over.mk σ ⟶ G.U)
    {y : Over.mk σ ⟶ G.U} (p : G.PointHom σ x y) :
    (f.mapPoints σ).obj x = x ≫ f.obj ∧
      ((f.mapPoints σ).map p).arrow = p.arrow ≫ f.arrow := sorry

end Hom

end GroupoidAlgebraicSpace

end AlgebraicGeometry
