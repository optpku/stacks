module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Groupoids in functors

This module bundles the object and arrow functors of a groupoid in functors on a
category, together with their structure maps and groupoid laws.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v w

namespace CategoryTheory

/-- A groupoid in functors on `C` consists of object and arrow functors, structure maps,
and groupoid laws. In `pullback s t`, the first projection is the later arrow and the
second projection is the earlier arrow. -/
structure GroupoidInFunctors (C : Type u) [Category.{v} C] where
  /-- The functor of objects. -/
  U : C ⥤ Type w
  /-- The functor of arrows. -/
  R : C ⥤ Type w
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
  /-- Composition is associative on generalized arrows. -/
  associativity :
    ∀ {W : C ⥤ Type w} (a b d : W ⟶ R)
      (h_ab : a ≫ s = b ≫ t) (h_bd : b ≫ s = d ≫ t)
      (h_ab_d : (pullback.lift a b h_ab ≫ c) ≫ s = d ≫ t)
      (h_a_bd : a ≫ s = (pullback.lift b d h_bd ≫ c) ≫ t),
      pullback.lift (pullback.lift a b h_ab ≫ c) d h_ab_d ≫ c =
        pullback.lift a (pullback.lift b d h_bd ≫ c) h_a_bd ≫ c
  /-- Composing an arrow with the identity at its source does not change it. -/
  right_identity :
    ∀ {W : C ⥤ Type w} (a : W ⟶ R)
      (h : a ≫ s = ((a ≫ s) ≫ e) ≫ t),
      pullback.lift a ((a ≫ s) ≫ e) h ≫ c = a
  /-- Composing the identity at the target of an arrow with that arrow does not change it. -/
  left_identity :
    ∀ {W : C ⥤ Type w} (a : W ⟶ R)
      (h : ((a ≫ t) ≫ e) ≫ s = a ≫ t),
      pullback.lift ((a ≫ t) ≫ e) a h ≫ c = a
  /-- Composing an arrow after its inverse gives the identity at its target. -/
  inverse_comp :
    ∀ {W : C ⥤ Type w} (a : W ⟶ R)
      (h : a ≫ s = (a ≫ i) ≫ t),
      pullback.lift a (a ≫ i) h ≫ c = (a ≫ t) ≫ e
  /-- Composing the inverse of an arrow after it gives the identity at its source. -/
  comp_inverse :
    ∀ {W : C ⥤ Type w} (a : W ⟶ R)
      (h : (a ≫ i) ≫ s = a ≫ t),
      pullback.lift (a ≫ i) a h ≫ c = (a ≫ s) ≫ e

namespace GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

/-- The discrete groupoid in functors on a functor `U`. -/
def discrete (U : C ⥤ Type w) : GroupoidInFunctors.{u, v, w} C where
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

/-- The object functor of the discrete groupoid is `U`. -/
theorem discrete_U (U : C ⥤ Type w) : (discrete U).U = U := sorry

/-- The arrow functor of the discrete groupoid is `U`. -/
theorem discrete_R (U : C ⥤ Type w) : (discrete U).R = U := sorry

/-- The source map of the discrete groupoid is the identity. -/
theorem discrete_s (U : C ⥤ Type w) : (discrete U).s = 𝟙 U := sorry

/-- The target map of the discrete groupoid is the identity. -/
theorem discrete_t (U : C ⥤ Type w) : (discrete U).t = 𝟙 U := sorry

/-- The composition map of the discrete groupoid is the first pullback projection. -/
theorem discrete_c (U : C ⥤ Type w) :
    (discrete U).c = pullback.fst (𝟙 U) (𝟙 U) := sorry

/-- The identity map of the discrete groupoid is the identity. -/
theorem discrete_e (U : C ⥤ Type w) : (discrete U).e = 𝟙 U := sorry

/-- The inverse map of the discrete groupoid is the identity. -/
theorem discrete_i (U : C ⥤ Type w) : (discrete U).i = 𝟙 U := sorry

/-- Compose two generalized arrows whose source and target agree. -/
def compose (G : GroupoidInFunctors.{u, v, w} C) {W : C ⥤ Type w} (a b : W ⟶ G.R)
    (h : a ≫ G.s = b ≫ G.t) : W ⟶ G.R :=
  pullback.lift a b h ≫ G.c

/-- The source of a pointwise composite is the source of its earlier arrow. -/
theorem compose_source (G : GroupoidInFunctors.{u, v, w} C) {W : C ⥤ Type w} (a b : W ⟶ G.R)
    (h : a ≫ G.s = b ≫ G.t) : G.compose a b h ≫ G.s = b ≫ G.s := sorry

/-- The target of a pointwise composite is the target of its later arrow. -/
theorem compose_target (G : GroupoidInFunctors.{u, v, w} C) {W : C ⥤ Type w} (a b : W ⟶ G.R)
    (h : a ≫ G.s = b ≫ G.t) : G.compose a b h ≫ G.t = a ≫ G.t := sorry

/-- Compose two arrows in the evaluation at an object `T`. -/
def composePoints (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (later earlier : G.R.obj T)
    (h : G.s.app T later = G.t.app T earlier) : G.R.obj T :=
  G.c.app T <|
    (pullbackObjIso G.s G.t T :
        (pullback G.s G.t).obj T ≅ pullback (G.s.app T) (G.t.app T)).inv <|
      (CategoryTheory.Limits.Types.pullbackIsoPullback (G.s.app T) (G.t.app T)).inv
        (⟨(later, earlier), h⟩ : Types.PullbackObj (G.s.app T) (G.t.app T))

/-- The source of an evaluated composite is the source of its earlier arrow. -/
theorem composePoints_source (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (later earlier : G.R.obj T) (h : G.s.app T later = G.t.app T earlier) :
    G.s.app T (G.composePoints T later earlier h) = G.s.app T earlier := sorry

/-- The target of an evaluated composite is the target of its later arrow. -/
theorem composePoints_target (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (later earlier : G.R.obj T) (h : G.s.app T later = G.t.app T earlier) :
    G.t.app T (G.composePoints T later earlier h) = G.t.app T later := sorry

/-- A morphism between two objects of the evaluation of a groupoid in functors. -/
structure PointHom (G : GroupoidInFunctors.{u, v, w} C) (T : C) (x y : G.U.obj T) where
  /-- The underlying arrow at `T`. -/
  arrow : G.R.obj T
  /-- The arrow has source `x`. -/
  source : G.s.app T arrow = x
  /-- The arrow has target `y`. -/
  target : G.t.app T arrow = y

namespace PointHom

/-- Construct a pointwise morphism from an arrow with specified endpoints. -/
def ofArrow {G : GroupoidInFunctors.{u, v, w} C} {T : C} {x y : G.U.obj T} (arrow : G.R.obj T)
    (source : G.s.app T arrow = x) (target : G.t.app T arrow = y) :
    G.PointHom T x y :=
  ⟨arrow, source, target⟩

/-- The underlying arrow of `ofArrow` is the supplied arrow. -/
theorem ofArrow_arrow {G : GroupoidInFunctors.{u, v, w} C} {T : C} {x y : G.U.obj T}
    (arrow : G.R.obj T) (source : G.s.app T arrow = x)
    (target : G.t.app T arrow = y) :
    (ofArrow arrow source target).arrow = arrow := sorry

/-- Pointwise morphisms with the same underlying arrow are equal. -/
theorem ext {G : GroupoidInFunctors.{u, v, w} C} {T : C} {x y : G.U.obj T}
    {f g : G.PointHom T x y} (h : f.arrow = g.arrow) : f = g := sorry

/-- Source and target of a pointwise arrow are the components of `s` and `t`. -/
theorem spec {G : GroupoidInFunctors.{u, v, w} C} {T : C} {x y : G.U.obj T}
    (p : G.PointHom T x y) :
    G.s.app T p.arrow = x ∧ G.t.app T p.arrow = y := sorry

end PointHom

/-- The explicit groupoid structure on the evaluation of a groupoid in functors at `T`. -/
@[reducible]
def pointGroupoid (G : GroupoidInFunctors.{u, v, w} C) (T : C) : Groupoid.{w, w} (G.U.obj T) where
  Hom := fun x y ↦ G.PointHom T x y
  id := fun x ↦
    { arrow := G.e.app T x
      source := sorry
      target := sorry }
  comp := fun f g ↦
    { arrow := G.composePoints T g.arrow f.arrow (g.source.trans f.target.symm)
      source := sorry
      target := sorry }
  id_comp := sorry
  comp_id := sorry
  assoc := sorry
  inv := fun f ↦
    { arrow := G.i.app T f.arrow
      source := sorry
      target := sorry }
  inv_comp := sorry
  comp_inv := sorry

/-- The bundled groupoid of the evaluation of a groupoid in functors at `T`. -/
def groupoidPoints (G : GroupoidInFunctors.{u, v, w} C) (T : C) : Grpd.{w, w} :=
  ⟨G.U.obj T, G.pointGroupoid T⟩

/-- The objects of `groupoidPoints G T` are the values of the object functor at `T`. -/
theorem groupoidPoints_obj (G : GroupoidInFunctors.{u, v, w} C) (T : C) :
    (G.groupoidPoints T : Type w) = G.U.obj T := sorry

/-- Evaluation at `T` is a groupoid whose morphisms from `x` to `y` are arrows in
`G.R.obj T` with source `x` and target `y`. -/
theorem pointGroupoid_spec (G : GroupoidInFunctors.{u, v, w} C) (T : C) (x y : G.U.obj T) :
    (G.pointGroupoid T).Hom x y = G.PointHom T x y := sorry

/-- The canonical map between composable-arrow pullbacks induced by maps of objects and arrows. -/
def composableMap {G H : GroupoidInFunctors.{u, v, w} C} (obj : G.U ⟶ H.U) (arrow : G.R ⟶ H.R)
    (map_s : G.s ≫ obj = arrow ≫ H.s) (map_t : G.t ≫ obj = arrow ≫ H.t) :
    pullback G.s G.t ⟶ pullback H.s H.t :=
  pullback.map G.s G.t H.s H.t arrow arrow obj map_s map_t

/-- The first projection of `composableMap` is the arrow map after the first projection. -/
theorem composableMap_fst {G H : GroupoidInFunctors.{u, v, w} C} (obj : G.U ⟶ H.U)
    (arrow : G.R ⟶ H.R) (map_s : G.s ≫ obj = arrow ≫ H.s)
    (map_t : G.t ≫ obj = arrow ≫ H.t) :
    composableMap obj arrow map_s map_t ≫ pullback.fst H.s H.t =
      pullback.fst G.s G.t ≫ arrow := sorry

/-- The second projection of `composableMap` is the arrow map after the second projection. -/
theorem composableMap_snd {G H : GroupoidInFunctors.{u, v, w} C} (obj : G.U ⟶ H.U)
    (arrow : G.R ⟶ H.R) (map_s : G.s ≫ obj = arrow ≫ H.s)
    (map_t : G.t ≫ obj = arrow ≫ H.t) :
    composableMap obj arrow map_s map_t ≫ pullback.snd H.s H.t =
      pullback.snd G.s G.t ≫ arrow := sorry

/-- A morphism of groupoids in functors consists of compatible maps on objects and arrows. -/
structure Hom (G H : GroupoidInFunctors.{u, v, w} C) where
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

/-- The identity morphism of a groupoid in functors. -/
def id (G : GroupoidInFunctors.{u, v, w} C) : Hom G G where
  obj := 𝟙 G.U
  arrow := 𝟙 G.R
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of the identity morphism is the identity. -/
theorem id_obj (G : GroupoidInFunctors.{u, v, w} C) : (id G).obj = 𝟙 G.U := sorry

/-- The arrow component of the identity morphism is the identity. -/
theorem id_arrow (G : GroupoidInFunctors.{u, v, w} C) : (id G).arrow = 𝟙 G.R := sorry

/-- Composition of morphisms of groupoids in functors. -/
def comp {G H K : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) (g : Hom H K) : Hom G K where
  obj := f.obj ≫ g.obj
  arrow := f.arrow ≫ g.arrow
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of a composite is the composite of the object components. -/
theorem comp_obj {G H K : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) (g : Hom H K) :
    (comp f g).obj = f.obj ≫ g.obj := sorry

/-- The arrow component of a composite is the composite of the arrow components. -/
theorem comp_arrow {G H K : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) (g : Hom H K) :
    (comp f g).arrow = f.arrow ≫ g.arrow := sorry

/-- Morphisms of groupoids in functors are determined by their object and arrow maps. -/
theorem ext {G H : GroupoidInFunctors.{u, v, w} C} {f g : Hom G H}
    (h_obj : f.obj = g.obj) (h_arrow : f.arrow = g.arrow) : f = g := sorry

/-- A morphism of groupoids in functors preserves identity arrows. -/
theorem map_e {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    G.e ≫ f.arrow = f.obj ≫ H.e := sorry

/-- A morphism of groupoids in functors preserves inverse arrows. -/
theorem map_i {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    G.i ≫ f.arrow = f.arrow ≫ H.i := sorry

/-- The induced map on pullbacks of the source and target maps. -/
def composableMap {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    pullback G.s G.t ⟶ pullback H.s H.t :=
  GroupoidInFunctors.composableMap f.obj f.arrow f.map_s f.map_t

/-- The first projection of `f.composableMap` is the arrow map after the first projection. -/
theorem composableMap_fst {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    f.composableMap ≫ pullback.fst H.s H.t = pullback.fst G.s G.t ≫ f.arrow := sorry

/-- The second projection of `f.composableMap` is the arrow map after the second projection. -/
theorem composableMap_snd {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    f.composableMap ≫ pullback.snd H.s H.t = pullback.snd G.s G.t ≫ f.arrow := sorry

/-- The functor of evaluations induced by a morphism of groupoids in functors. -/
def mapPoints {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) (T : C) :
    (G.groupoidPoints T : Grpd.{w, w}) ⥤ (H.groupoidPoints T : Grpd.{w, w}) where
  obj := fun x ↦ f.obj.app T x
  map := fun {x y} (p : G.PointHom T x y) ↦
    PointHom.ofArrow (f.arrow.app T p.arrow) sorry sorry
  map_id := sorry
  map_comp := sorry

/-- On objects, the induced functor on points is the object-map component at `T`. -/
theorem mapPoints_obj {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) (T : C)
    (x : G.U.obj T) : (f.mapPoints T).obj x = f.obj.app T x := sorry

/-- On arrows, the induced functor on points is the arrow-map component at `T`. -/
theorem mapPoints_map_arrow {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H)
    (T : C) {x y : G.U.obj T} (p : G.PointHom T x y) :
    ((f.mapPoints T).map p).arrow = f.arrow.app T p.arrow := sorry

end Hom

/-- The functor `C ⥤ Grpd` sending each object to the evaluation groupoid. -/
def toFunctor (G : GroupoidInFunctors.{u, v, w} C) : C ⥤ Grpd.{w, w} where
  obj T := G.groupoidPoints T
  map {T T'} (f : T ⟶ T') :=
    { obj := fun x ↦ G.U.map f x
      map := fun {x y} (p : G.PointHom T x y) ↦
        PointHom.ofArrow (G.R.map f p.arrow) sorry sorry
      map_id := sorry
      map_comp := sorry }
  map_id := sorry
  map_comp := sorry

/-- `toFunctor` evaluates to the point groupoid at each object. -/
theorem toFunctor_obj (G : GroupoidInFunctors.{u, v, w} C) (T : C) :
    (toFunctor G).obj T = G.groupoidPoints T := sorry

end GroupoidInFunctors

end CategoryTheory
