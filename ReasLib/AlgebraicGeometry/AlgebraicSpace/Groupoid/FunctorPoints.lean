/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Small functor-of-points groupoids

Functor-of-points elements and arrows form groupoids with small object and Hom types.
Restriction along morphisms of schemes makes these groupoids into a presheaf.
-/

@[expose] public section

-- Exposed constructions use private endpoint and functor laws in their proof fields.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry Limits Opposite AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A morphism between two `T`-valued functor-of-points of a groupoid in algebraic spaces. -/
structure FunctorPointHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S}
    (x y : G.U.left.functorOfPoints.obj (op T)) where
  /-- The underlying `T`-valued arrow of `R`. -/
  arrow : G.R.left.functorOfPoints.obj (op T)
  /-- The arrow has source `x`. -/
  source : G.s.left.app (op T) arrow = x
  /-- The arrow has target `y`. -/
  target : G.t.left.app (op T) arrow = y

namespace FunctorPointHom

/-- Construct a morphism of functor-of-points from an arrow with specified endpoints. -/
def ofArrow {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : G.U.left.functorOfPoints.obj (op T)}
    (arrow : G.R.left.functorOfPoints.obj (op T))
    (source : G.s.left.app (op T) arrow = x)
    (target : G.t.left.app (op T) arrow = y) :
    G.FunctorPointHom x y :=
  ⟨arrow, source, target⟩

/-- The underlying arrow of `ofArrow` is the supplied arrow. -/
theorem ofArrow_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S}
    {x y : G.U.left.functorOfPoints.obj (op T)}
    (arrow : G.R.left.functorOfPoints.obj (op T))
    (source : G.s.left.app (op T) arrow = x)
    (target : G.t.left.app (op T) arrow = y) :
    (ofArrow arrow source target).arrow = arrow := sorry

/-- Morphisms of functor-of-points with the same underlying arrow are equal. -/
theorem ext {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : G.U.left.functorOfPoints.obj (op T)}
    {f g : G.FunctorPointHom x y} (h : f.arrow = g.arrow) : f = g := sorry

/-- The Yoneda morphism `ofOver T ⟶ G.R.left` associated to a functor-of-points arrow. -/
def toHom {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) : ofOver T ⟶ G.R.left :=
  yonedaEquiv.symm f.arrow

/-- `toHom` is the Yoneda equivalent of the underlying arrow. -/
theorem toHom_eq {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) :
    f.toHom = yonedaEquiv.symm f.arrow := sorry

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}

/-- Composable functor-of-points arrows have the same map to the base space. -/
private theorem compArrow_over {T : Over S}
    {x y z : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) (g : G.FunctorPointHom y z) :
    g.toHom ≫ G.R.hom = f.toHom ≫ G.R.hom := sorry

/-- The lifts of composable functor-of-points arrows are composable over the base space. -/
private theorem compArrow_compatible {T : Over S}
    {x y z : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) (g : G.FunctorPointHom y z) :
    (Over.homMk g.toHom (compArrow_over f g) :
        Over.mk (f.toHom ≫ G.R.hom) ⟶ G.R) ≫ G.s =
      (Over.homMk f.toHom rfl : Over.mk (f.toHom ≫ G.R.hom) ⟶ G.R) ≫ G.t := sorry

/-- Composition of functor-of-points arrows is induced by groupoid composition. -/
def compArrow {T : Over S} {x y z : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) (g : G.FunctorPointHom y z) :
    G.R.left.functorOfPoints.obj (op T) :=
  let later : Over.mk (f.toHom ≫ G.R.hom) ⟶ G.R :=
    Over.homMk g.toHom (compArrow_over f g)
  let earlier : Over.mk (f.toHom ≫ G.R.hom) ⟶ G.R := Over.homMk f.toHom rfl
  yonedaEquiv ((G.compose later earlier (compArrow_compatible f g)).left :
    yoneda.obj T ⟶ G.R.left.functorOfPoints)

/-- A composite arrow has the source of the first arrow and the target of the second. -/
private theorem comp_endpoints {T : Over S}
    {x y z : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) (g : G.FunctorPointHom y z) :
    G.s.left.app (op T) (compArrow f g) = x ∧
      G.t.left.app (op T) (compArrow f g) = z := sorry

/-- The composite morphism of functor-of-points. -/
def comp {T : Over S} {x y z : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) (g : G.FunctorPointHom y z) :
    G.FunctorPointHom x z :=
  ofArrow (compArrow f g) (comp_endpoints f g).1 (comp_endpoints f g).2

/-- The underlying arrow of a composite is `compArrow`. -/
theorem comp_arrow {T : Over S} {x y z : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) (g : G.FunctorPointHom y z) :
    (f.comp g).arrow = compArrow f g := sorry

/-- The identity arrow at a point has that point as both endpoints. -/
private theorem id_endpoints {T : Over S} (x : G.U.left.functorOfPoints.obj (op T)) :
    G.s.left.app (op T) (G.e.left.app (op T) x) = x ∧
      G.t.left.app (op T) (G.e.left.app (op T) x) = x := sorry

/-- The identity morphism of a functor-of-points object. -/
def id {T : Over S} (x : G.U.left.functorOfPoints.obj (op T)) :
    G.FunctorPointHom x x :=
  ofArrow (G.e.left.app (op T) x) (id_endpoints x).1 (id_endpoints x).2

/-- Inversion exchanges the endpoints of a functor-of-points arrow. -/
private theorem inv_endpoints {T : Over S}
    {x y : G.U.left.functorOfPoints.obj (op T)} (f : G.FunctorPointHom x y) :
    G.s.left.app (op T) (G.i.left.app (op T) f.arrow) = y ∧
      G.t.left.app (op T) (G.i.left.app (op T) f.arrow) = x := sorry

/-- The inverse morphism is induced by the groupoid inverse map. -/
def inv {T : Over S} {x y : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) : G.FunctorPointHom y x :=
  ofArrow (G.i.left.app (op T) f.arrow) (inv_endpoints f).1 (inv_endpoints f).2

/-- Identity arrows are left identities for functor-of-points composition. -/
private theorem id_comp {T : Over S} {x y : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) : comp (id x) f = f := sorry

/-- Identity arrows are right identities for functor-of-points composition. -/
private theorem comp_id {T : Over S} {x y : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) : comp f (id y) = f := sorry

/-- Composition of functor-of-points arrows is associative. -/
private theorem assoc {T : Over S} {w x y z : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom w x) (g : G.FunctorPointHom x y)
    (h : G.FunctorPointHom y z) : comp (comp f g) h = comp f (comp g h) := sorry

/-- An inverse composed with its arrow is the identity at the target. -/
private theorem inv_comp {T : Over S} {x y : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) : comp (inv f) f = id y := sorry

/-- An arrow composed with its inverse is the identity at the source. -/
private theorem comp_inv {T : Over S} {x y : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) : comp f (inv f) = id x := sorry

/-- Restriction of an arrow has the restricted endpoints. -/
private theorem restrict_endpoints {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    {x y : G.U.left.functorOfPoints.obj T} (p : G.FunctorPointHom x y) :
    G.s.left.app T' (G.R.left.functorOfPoints.map f p.arrow) =
        G.U.left.functorOfPoints.map f x ∧
      G.t.left.app T' (G.R.left.functorOfPoints.map f p.arrow) =
        G.U.left.functorOfPoints.map f y := sorry

/-- Restriction of a functor-of-points morphism along a morphism of test schemes. -/
def restrict {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    {x y : G.U.left.functorOfPoints.obj T} (p : G.FunctorPointHom x y) :
    G.FunctorPointHom (G.U.left.functorOfPoints.map f x)
      (G.U.left.functorOfPoints.map f y) :=
  ofArrow (G.R.left.functorOfPoints.map f p.arrow)
    (restrict_endpoints f p).1 (restrict_endpoints f p).2

/-- Restriction preserves identity functor-of-points arrows. -/
private theorem restrict_id {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    (x : G.U.left.functorOfPoints.obj T) :
    restrict f (id x) = id (G.U.left.functorOfPoints.map f x) := sorry

/-- Restriction preserves composition of functor-of-points arrows. -/
private theorem restrict_comp {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    {x y z : G.U.left.functorOfPoints.obj T}
    (p : G.FunctorPointHom x y) (q : G.FunctorPointHom y z) :
    restrict f (comp p q) = comp (restrict f p) (restrict f q) := sorry

end FunctorPointHom

/-- The groupoid of functor-of-points objects has small arrow types. -/
@[reducible]
def functorPointGroupoid {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (T : Over S) :
    CategoryTheory.Groupoid.{u, u} (G.U.left.functorOfPoints.obj (op T)) where
  Hom := fun x y ↦ G.FunctorPointHom x y
  id := FunctorPointHom.id
  comp := FunctorPointHom.comp
  id_comp := FunctorPointHom.id_comp
  comp_id := FunctorPointHom.comp_id
  assoc := FunctorPointHom.assoc
  inv := FunctorPointHom.inv
  inv_comp := FunctorPointHom.inv_comp
  comp_inv := FunctorPointHom.comp_inv

/-- The bundled small groupoid of functor-of-points over a test scheme. -/
def functorPoints {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (T : Over S) : Grpd.{u, u} :=
  ⟨G.U.left.functorOfPoints.obj (op T), G.functorPointGroupoid T⟩

/-- Morphisms in `functorPointGroupoid G T` are `FunctorPointHom`. -/
theorem functorPointGroupoid_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (T : Over S)
    (x y : G.U.left.functorOfPoints.obj (op T)) :
    (G.functorPointGroupoid T).Hom x y = G.FunctorPointHom x y := sorry

/-- The objects of `functorPoints G T` are the `T`-valued points of `U`. -/
theorem functorPoints_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (T : Over S) :
    (G.functorPoints T : Type u) = G.U.left.functorOfPoints.obj (op T) := sorry

/-- Restriction along a morphism of test schemes defines a functor on point groupoids. -/
def functorPointsMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    G.functorPoints T.unop ⥤ G.functorPoints T'.unop where
  obj := G.U.left.functorOfPoints.map f
  map := FunctorPointHom.restrict f
  map_id := FunctorPointHom.restrict_id f
  map_comp := FunctorPointHom.restrict_comp f

/-- Restriction along an identity is the identity functor on the point groupoid. -/
private theorem functorPointsMap_id {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (T : (Over S)ᵒᵖ) :
    G.functorPointsMap (𝟙 T) = 𝟭 (G.functorPoints T.unop) := sorry

/-- Restriction along a composite is the composite of the restriction functors. -/
private theorem functorPointsMap_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' T'' : (Over S)ᵒᵖ}
    (f : T ⟶ T') (g : T' ⟶ T'') :
    G.functorPointsMap (f ≫ g) = G.functorPointsMap f ⋙ G.functorPointsMap g := sorry

/-- The presheaf of small groupoids of functor-of-points of an algebraic-space groupoid. -/
def groupoidPresheaf {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (Over S)ᵒᵖ ⥤ Grpd.{u, u} where
  obj T := G.functorPoints T.unop
  map := G.functorPointsMap
  map_id := functorPointsMap_id G
  map_comp := functorPointsMap_comp G

/-- The objects of the point groupoid over `T` are the `T`-valued points of `U`. -/
theorem groupoidPresheaf_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (T : Over S) :
    (G.groupoidPresheaf.obj (op T) : Type u) = G.U.left.functorOfPoints.obj (op T) :=
  sorry

/-- Restriction of objects in `groupoidPresheaf` is restriction of functor-of-points of `U`. -/
theorem groupoidPresheaf_map_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    (x : G.U.left.functorOfPoints.obj T) :
    (G.groupoidPresheaf.map f).obj x = G.U.left.functorOfPoints.map f x := sorry

/-- Restriction of arrows in `groupoidPresheaf` is restriction of functor-of-points of `R`. -/
theorem groupoidPresheaf_map_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' : Over S} (f : op T ⟶ op T')
    {x y : G.U.left.functorOfPoints.obj (op T)} (p : G.FunctorPointHom x y) :
    ((G.groupoidPresheaf.map f).map p).arrow = G.R.left.functorOfPoints.map f p.arrow :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
