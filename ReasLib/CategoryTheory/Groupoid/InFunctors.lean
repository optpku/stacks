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

/-- The first projection of the identity pullback has the source of the second projection. -/
private theorem discrete_comp_source (U : C ⥤ Type w) :
    pullback.fst (𝟙 U) (𝟙 U) ≫ 𝟙 U = pullback.snd (𝟙 U) (𝟙 U) ≫ 𝟙 U := sorry

/-- The first projection of the identity pullback preserves its target. -/
private theorem discrete_comp_target (U : C ⥤ Type w) :
    pullback.fst (𝟙 U) (𝟙 U) ≫ 𝟙 U = pullback.fst (𝟙 U) (𝟙 U) ≫ 𝟙 U := sorry

/-- The identity natural transformation preserves the source of a discrete arrow. -/
private theorem discrete_identity_source (U : C ⥤ Type w) : 𝟙 U ≫ 𝟙 U = 𝟙 U := sorry

/-- The identity natural transformation preserves the target of a discrete arrow. -/
private theorem discrete_identity_target (U : C ⥤ Type w) : 𝟙 U ≫ 𝟙 U = 𝟙 U := sorry

/-- Inversion in a discrete groupoid exchanges source and target. -/
private theorem discrete_inverse_source (U : C ⥤ Type w) : 𝟙 U ≫ 𝟙 U = 𝟙 U := sorry

/-- Inversion in a discrete groupoid exchanges target and source. -/
private theorem discrete_inverse_target (U : C ⥤ Type w) : 𝟙 U ≫ 𝟙 U = 𝟙 U := sorry

/-- Composition through the first projection of the identity pullback is associative. -/
private theorem discrete_associativity (U : C ⥤ Type w) {W : C ⥤ Type w}
    (a b d : W ⟶ U) (h_ab : a ≫ 𝟙 U = b ≫ 𝟙 U) (h_bd : b ≫ 𝟙 U = d ≫ 𝟙 U)
    (h_ab_d : (pullback.lift a b h_ab ≫ pullback.fst (𝟙 U) (𝟙 U)) ≫ 𝟙 U = d ≫ 𝟙 U)
    (h_a_bd : a ≫ 𝟙 U = (pullback.lift b d h_bd ≫ pullback.fst (𝟙 U) (𝟙 U)) ≫ 𝟙 U) :
    pullback.lift (pullback.lift a b h_ab ≫ pullback.fst (𝟙 U) (𝟙 U)) d h_ab_d ≫
        pullback.fst (𝟙 U) (𝟙 U) =
      pullback.lift a (pullback.lift b d h_bd ≫ pullback.fst (𝟙 U) (𝟙 U)) h_a_bd ≫
        pullback.fst (𝟙 U) (𝟙 U) := sorry

/-- Discrete arrows are unchanged by composition with their source identity. -/
private theorem discrete_right_identity (U : C ⥤ Type w) {W : C ⥤ Type w} (a : W ⟶ U)
    (h : a ≫ 𝟙 U = ((a ≫ 𝟙 U) ≫ 𝟙 U) ≫ 𝟙 U) :
    pullback.lift a ((a ≫ 𝟙 U) ≫ 𝟙 U) h ≫ pullback.fst (𝟙 U) (𝟙 U) = a := sorry

/-- Discrete arrows are unchanged by composition with their target identity. -/
private theorem discrete_left_identity (U : C ⥤ Type w) {W : C ⥤ Type w} (a : W ⟶ U)
    (h : ((a ≫ 𝟙 U) ≫ 𝟙 U) ≫ 𝟙 U = a ≫ 𝟙 U) :
    pullback.lift ((a ≫ 𝟙 U) ≫ 𝟙 U) a h ≫ pullback.fst (𝟙 U) (𝟙 U) = a := sorry

/-- A discrete arrow composed after its inverse is its target identity. -/
private theorem discrete_inverse_comp (U : C ⥤ Type w) {W : C ⥤ Type w} (a : W ⟶ U)
    (h : a ≫ 𝟙 U = (a ≫ 𝟙 U) ≫ 𝟙 U) :
    pullback.lift a (a ≫ 𝟙 U) h ≫ pullback.fst (𝟙 U) (𝟙 U) = (a ≫ 𝟙 U) ≫ 𝟙 U := sorry

/-- The inverse of a discrete arrow composed after it is its source identity. -/
private theorem discrete_comp_inverse (U : C ⥤ Type w) {W : C ⥤ Type w} (a : W ⟶ U)
    (h : (a ≫ 𝟙 U) ≫ 𝟙 U = a ≫ 𝟙 U) :
    pullback.lift (a ≫ 𝟙 U) a h ≫ pullback.fst (𝟙 U) (𝟙 U) = (a ≫ 𝟙 U) ≫ 𝟙 U := sorry

/-- The discrete groupoid in functors on a functor `U`. -/
def discrete (U : C ⥤ Type w) : GroupoidInFunctors.{u, v, w} C where
  U := U
  R := U
  s := 𝟙 U
  t := 𝟙 U
  c := pullback.fst (𝟙 U) (𝟙 U)
  e := 𝟙 U
  i := 𝟙 U
  comp_source := private discrete_comp_source U
  comp_target := private discrete_comp_target U
  identity_source := private discrete_identity_source U
  identity_target := private discrete_identity_target U
  inverse_source := private discrete_inverse_source U
  inverse_target := private discrete_inverse_target U
  associativity := private discrete_associativity U
  right_identity := private discrete_right_identity U
  left_identity := private discrete_left_identity U
  inverse_comp := private discrete_inverse_comp U
  comp_inverse := private discrete_comp_inverse U

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

/-- The identity arrow at an evaluated object has that object as its source. -/
private theorem pointIdentity_source (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (x : G.U.obj T) : G.s.app T (G.e.app T x) = x := sorry

/-- The identity arrow at an evaluated object has that object as its target. -/
private theorem pointIdentity_target (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (x : G.U.obj T) : G.t.app T (G.e.app T x) = x := sorry

/-- The source of an evaluated inverse arrow is the target of the original arrow. -/
private theorem pointInverse_source (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    {x y : G.U.obj T} (p : G.PointHom T x y) : G.s.app T (G.i.app T p.arrow) = y := sorry

/-- The target of an evaluated inverse arrow is the source of the original arrow. -/
private theorem pointInverse_target (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    {x y : G.U.obj T} (p : G.PointHom T x y) : G.t.app T (G.i.app T p.arrow) = x := sorry

namespace PointHom

/-- The identity pointwise morphism has the arrow supplied by the identity natural transformation. -/
def id (G : GroupoidInFunctors.{u, v, w} C) (T : C) (x : G.U.obj T) : G.PointHom T x x where
  arrow := G.e.app T x
  source := private pointIdentity_source G T x
  target := private pointIdentity_target G T x

/-- Composition of pointwise morphisms uses the evaluated pullback composition. -/
def comp {G : GroupoidInFunctors.{u, v, w} C} {T : C} {x y z : G.U.obj T}
    (earlier : G.PointHom T x y) (later : G.PointHom T y z) : G.PointHom T x z :=
  ofArrow (G.composePoints T later.arrow earlier.arrow (later.source.trans earlier.target.symm))
    ((G.composePoints_source T later.arrow earlier.arrow
      (later.source.trans earlier.target.symm)).trans earlier.source)
    ((G.composePoints_target T later.arrow earlier.arrow
      (later.source.trans earlier.target.symm)).trans later.target)

/-- Inversion of a pointwise morphism uses the inverse natural transformation. -/
def inv {G : GroupoidInFunctors.{u, v, w} C} {T : C} {x y : G.U.obj T}
    (p : G.PointHom T x y) : G.PointHom T y x where
  arrow := G.i.app T p.arrow
  source := private pointInverse_source G T p
  target := private pointInverse_target G T p

/-- Identity pointwise morphisms are left identities for composition. -/
private theorem id_comp {G : GroupoidInFunctors.{u, v, w} C} {T : C} {x y : G.U.obj T}
    (p : G.PointHom T x y) : comp (id G T x) p = p := sorry

/-- Identity pointwise morphisms are right identities for composition. -/
private theorem comp_id {G : GroupoidInFunctors.{u, v, w} C} {T : C} {x y : G.U.obj T}
    (p : G.PointHom T x y) : comp p (id G T y) = p := sorry

/-- Composition of pointwise morphisms is associative. -/
private theorem assoc {G : GroupoidInFunctors.{u, v, w} C} {T : C}
    {x y z target : G.U.obj T} (first : G.PointHom T x y) (second : G.PointHom T y z)
    (third : G.PointHom T z target) : comp (comp first second) third = comp first (comp second third) := sorry

/-- Composing a pointwise inverse before its original morphism gives a target identity. -/
private theorem inv_comp {G : GroupoidInFunctors.{u, v, w} C} {T : C} {x y : G.U.obj T}
    (p : G.PointHom T x y) : comp (inv p) p = id G T y := sorry

/-- Composing a pointwise inverse after its original morphism gives a source identity. -/
private theorem comp_inv {G : GroupoidInFunctors.{u, v, w} C} {T : C} {x y : G.U.obj T}
    (p : G.PointHom T x y) : comp p (inv p) = id G T x := sorry

end PointHom

/-- The explicit groupoid structure on the evaluation of a groupoid in functors at `T`. -/
@[reducible]
def pointGroupoid (G : GroupoidInFunctors.{u, v, w} C) (T : C) : Groupoid.{w, w} (G.U.obj T) where
  Hom := fun x y ↦ G.PointHom T x y
  id := PointHom.id G T
  comp := PointHom.comp
  id_comp := private PointHom.id_comp
  comp_id := private PointHom.comp_id
  assoc := private PointHom.assoc
  inv := PointHom.inv
  inv_comp := private PointHom.inv_comp
  comp_inv := private PointHom.comp_inv

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

/-- The evaluated groupoid identities and inverses are the components of the structure maps. -/
theorem pointGroupoid_operations_spec (G : GroupoidInFunctors.{u, v, w} C) (T : C) :
    (∀ x : G.U.obj T, ((G.pointGroupoid T).id x).arrow = G.e.app T x) ∧
      (∀ {x y : G.U.obj T} (p : G.PointHom T x y),
        ((G.pointGroupoid T).inv p).arrow = G.i.app T p.arrow) := sorry

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

/-- A groupoid morphism preserves both source and target. -/
theorem source_target_spec {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    (G.s ≫ f.obj = f.arrow ≫ H.s) ∧ (G.t ≫ f.obj = f.arrow ≫ H.t) := sorry

/-- Identity natural transformations commute with the source map. -/
private theorem id_map_s (G : GroupoidInFunctors.{u, v, w} C) :
    G.s ≫ 𝟙 G.U = 𝟙 G.R ≫ G.s := sorry

/-- Identity natural transformations commute with the target map. -/
private theorem id_map_t (G : GroupoidInFunctors.{u, v, w} C) :
    G.t ≫ 𝟙 G.U = 𝟙 G.R ≫ G.t := sorry

/-- Identity natural transformations preserve the composition map. -/
private theorem id_map_c (G : GroupoidInFunctors.{u, v, w} C) :
    G.c ≫ 𝟙 G.R =
      GroupoidInFunctors.composableMap (𝟙 G.U) (𝟙 G.R) (id_map_s G) (id_map_t G) ≫ G.c := sorry

/-- The identity morphism of a groupoid in functors. -/
def id (G : GroupoidInFunctors.{u, v, w} C) : Hom G G where
  obj := 𝟙 G.U
  arrow := 𝟙 G.R
  map_s := private id_map_s G
  map_t := private id_map_t G
  map_c := private id_map_c G

/-- The object component of the identity morphism is the identity. -/
theorem id_obj (G : GroupoidInFunctors.{u, v, w} C) : (id G).obj = 𝟙 G.U := sorry

/-- The arrow component of the identity morphism is the identity. -/
theorem id_arrow (G : GroupoidInFunctors.{u, v, w} C) : (id G).arrow = 𝟙 G.R := sorry

/-- Composite object and arrow maps commute with the source map. -/
private theorem comp_map_s {G H K : GroupoidInFunctors.{u, v, w} C}
    (f : Hom G H) (g : Hom H K) : G.s ≫ (f.obj ≫ g.obj) = (f.arrow ≫ g.arrow) ≫ K.s := sorry

/-- Composite object and arrow maps commute with the target map. -/
private theorem comp_map_t {G H K : GroupoidInFunctors.{u, v, w} C}
    (f : Hom G H) (g : Hom H K) : G.t ≫ (f.obj ≫ g.obj) = (f.arrow ≫ g.arrow) ≫ K.t := sorry

/-- Composite object and arrow maps preserve the composition map. -/
private theorem comp_map_c {G H K : GroupoidInFunctors.{u, v, w} C}
    (f : Hom G H) (g : Hom H K) :
    G.c ≫ (f.arrow ≫ g.arrow) =
      GroupoidInFunctors.composableMap (f.obj ≫ g.obj) (f.arrow ≫ g.arrow)
        (comp_map_s f g) (comp_map_t f g) ≫ K.c := sorry

/-- Composition of morphisms of groupoids in functors. -/
def comp {G H K : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) (g : Hom H K) : Hom G K where
  obj := f.obj ≫ g.obj
  arrow := f.arrow ≫ g.arrow
  map_s := private comp_map_s f g
  map_t := private comp_map_t f g
  map_c := private comp_map_c f g

/-- The object component of a composite is the composite of the object components. -/
theorem comp_obj {G H K : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) (g : Hom H K) :
    (comp f g).obj = f.obj ≫ g.obj := sorry

/-- The arrow component of a composite is the composite of the arrow components. -/
theorem comp_arrow {G H K : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) (g : Hom H K) :
    (comp f g).arrow = f.arrow ≫ g.arrow := sorry

/-- Morphisms of groupoids in functors are determined by their object and arrow maps. -/
theorem ext {G H : GroupoidInFunctors.{u, v, w} C} {f g : Hom G H}
    (h_obj : f.obj = g.obj) (h_arrow : f.arrow = g.arrow) : f = g := sorry

/-- The identity groupoid morphism is a left identity for composition. -/
theorem id_comp {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    comp (id G) f = f := sorry

/-- The identity groupoid morphism is a right identity for composition. -/
theorem comp_id {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    comp f (id H) = f := sorry

/-- Composition of groupoid morphisms is associative. -/
theorem assoc {G H K L : GroupoidInFunctors.{u, v, w} C}
    (first : Hom G H) (second : Hom H K) (third : Hom K L) :
    comp (comp first second) third = comp first (comp second third) := sorry

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

/-- The evaluated arrow map of a groupoid morphism preserves the specified source. -/
private theorem mapPoints_source {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H)
    (T : C) {x y : G.U.obj T} (p : G.PointHom T x y) :
    H.s.app T (f.arrow.app T p.arrow) = f.obj.app T x := sorry

/-- The evaluated arrow map of a groupoid morphism preserves the specified target. -/
private theorem mapPoints_target {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H)
    (T : C) {x y : G.U.obj T} (p : G.PointHom T x y) :
    H.t.app T (f.arrow.app T p.arrow) = f.obj.app T y := sorry

/-- The evaluated object and arrow maps of a groupoid morphism preserve identity arrows. -/
private theorem mapPoints_id {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H)
    (T : C) (x : G.U.obj T) :
    PointHom.ofArrow (f.arrow.app T (PointHom.id G T x).arrow)
        (mapPoints_source f T (PointHom.id G T x)) (mapPoints_target f T (PointHom.id G T x)) =
      PointHom.id H T (f.obj.app T x) := sorry

/-- The evaluated object and arrow maps of a groupoid morphism preserve composition. -/
private theorem mapPoints_comp {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H)
    (T : C) {x y z : G.U.obj T} (earlier : G.PointHom T x y) (later : G.PointHom T y z) :
    PointHom.ofArrow (f.arrow.app T (PointHom.comp earlier later).arrow)
        (mapPoints_source f T (PointHom.comp earlier later))
        (mapPoints_target f T (PointHom.comp earlier later)) =
      PointHom.comp
        (PointHom.ofArrow (f.arrow.app T earlier.arrow)
          (mapPoints_source f T earlier) (mapPoints_target f T earlier))
        (PointHom.ofArrow (f.arrow.app T later.arrow)
          (mapPoints_source f T later) (mapPoints_target f T later)) := sorry

/-- The functor of evaluations induced by a morphism of groupoids in functors. -/
def mapPoints {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) (T : C) :
    (G.groupoidPoints T : Grpd.{w, w}) ⥤ (H.groupoidPoints T : Grpd.{w, w}) where
  obj := fun x ↦ f.obj.app T x
  map := fun {x y} (p : G.PointHom T x y) ↦
    { arrow := f.arrow.app T p.arrow
      source := private mapPoints_source f T p
      target := private mapPoints_target f T p }
  map_id := private mapPoints_id f T
  map_comp := private mapPoints_comp f T

/-- On objects, the induced functor on points is the object-map component at `T`. -/
theorem mapPoints_obj {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) (T : C)
    (x : G.U.obj T) : (f.mapPoints T).obj x = f.obj.app T x := sorry

/-- On arrows, the induced functor on points is the arrow-map component at `T`. -/
theorem mapPoints_map_arrow {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H)
    (T : C) {x y : G.U.obj T} (p : G.PointHom T x y) :
    ((f.mapPoints T).map p).arrow = f.arrow.app T p.arrow := sorry

end Hom

/-- The category of groupoids in functors has compatible object and arrow maps as morphisms. -/
@[reducible]
def category (C : Type u) [Category.{v} C] : Category.{max u w} (GroupoidInFunctors.{u, v, w} C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The arrow transition of an evaluated groupoid preserves the specified source. -/
private theorem mapPoints_source (G : GroupoidInFunctors.{u, v, w} C) {T T' : C}
    (transition : T ⟶ T') {x y : G.U.obj T} (p : G.PointHom T x y) :
    G.s.app T' (G.R.map transition p.arrow) = G.U.map transition x := sorry

/-- The arrow transition of an evaluated groupoid preserves the specified target. -/
private theorem mapPoints_target (G : GroupoidInFunctors.{u, v, w} C) {T T' : C}
    (transition : T ⟶ T') {x y : G.U.obj T} (p : G.PointHom T x y) :
    G.t.app T' (G.R.map transition p.arrow) = G.U.map transition y := sorry

/-- Transition maps of evaluated groupoids preserve identity arrows. -/
private theorem mapPoints_id (G : GroupoidInFunctors.{u, v, w} C) {T T' : C}
    (transition : T ⟶ T') (x : G.U.obj T) :
    PointHom.ofArrow (G.R.map transition (PointHom.id G T x).arrow)
        (mapPoints_source G transition (PointHom.id G T x))
        (mapPoints_target G transition (PointHom.id G T x)) =
      PointHom.id G T' (G.U.map transition x) := sorry

/-- Transition maps of evaluated groupoids preserve composition. -/
private theorem mapPoints_comp (G : GroupoidInFunctors.{u, v, w} C) {T T' : C}
    (transition : T ⟶ T') {x y z : G.U.obj T}
    (earlier : G.PointHom T x y) (later : G.PointHom T y z) :
    PointHom.ofArrow (G.R.map transition (PointHom.comp earlier later).arrow)
        (mapPoints_source G transition (PointHom.comp earlier later))
        (mapPoints_target G transition (PointHom.comp earlier later)) =
      PointHom.comp
        (PointHom.ofArrow (G.R.map transition earlier.arrow)
          (mapPoints_source G transition earlier) (mapPoints_target G transition earlier))
        (PointHom.ofArrow (G.R.map transition later.arrow)
          (mapPoints_source G transition later) (mapPoints_target G transition later)) := sorry

/-- A base-category morphism induces a functor between the evaluated groupoids. -/
def mapPoints (G : GroupoidInFunctors.{u, v, w} C) {T T' : C} (transition : T ⟶ T') :
    (G.groupoidPoints T : Grpd.{w, w}) ⥤ (G.groupoidPoints T' : Grpd.{w, w}) where
  obj := fun x ↦ G.U.map transition x
  map := fun {x y} (p : G.PointHom T x y) ↦
    { arrow := G.R.map transition p.arrow
      source := private mapPoints_source G transition p
      target := private mapPoints_target G transition p }
  map_id := private mapPoints_id G transition
  map_comp := private mapPoints_comp G transition

/-- Identity base morphisms induce identity functors of evaluated groupoids. -/
private theorem toFunctor_map_id (G : GroupoidInFunctors.{u, v, w} C) (T : C) :
    G.mapPoints (𝟙 T) = 𝟭 (G.groupoidPoints T) := sorry

/-- Composition of base morphisms induces composition of the evaluated functors. -/
private theorem toFunctor_map_comp (G : GroupoidInFunctors.{u, v, w} C) {T T' T'' : C}
    (first : T ⟶ T') (second : T' ⟶ T'') :
    G.mapPoints (first ≫ second) = G.mapPoints first ⋙ G.mapPoints second := sorry

/-- The functor `C ⥤ Grpd` sending each object to the evaluation groupoid. -/
def toFunctor (G : GroupoidInFunctors.{u, v, w} C) : C ⥤ Grpd.{w, w} where
  obj T := G.groupoidPoints T
  map := G.mapPoints
  map_id := private toFunctor_map_id G
  map_comp := private toFunctor_map_comp G

/-- `toFunctor` evaluates to the point groupoid at each object. -/
theorem toFunctor_obj (G : GroupoidInFunctors.{u, v, w} C) (T : C) :
    (toFunctor G).obj T = G.groupoidPoints T := sorry

end GroupoidInFunctors

end CategoryTheory
