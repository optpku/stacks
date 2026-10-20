/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid

/-!
# Scheme-valued points of a groupoid in algebraic spaces

This module constructs the contravariant groupoid-valued functor of scheme-valued
points of a groupoid in algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite AlgebraicSpace

noncomputable section

universe u

set_option maxHeartbeats 1000000 in
section

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A morphism between two scheme-valued points of a groupoid in algebraic spaces. -/
structure SpacePointHom {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (x y : ofOver T ⟶ G.U.left) where
  /-- The underlying scheme-valued arrow. -/
  arrow : ofOver T ⟶ G.R.left
  /-- The arrow has source `x`. -/
  source : arrow ≫ G.s.left = x
  /-- The arrow has target `y`. -/
  target : arrow ≫ G.t.left = y

namespace SpacePointHom

/-- Construct a morphism of scheme-valued points from an arrow with specified endpoints. -/
def ofArrow {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : ofOver T ⟶ G.U.left} (arrow : ofOver T ⟶ G.R.left)
    (source : arrow ≫ G.s.left = x) (target : arrow ≫ G.t.left = y) :
    G.SpacePointHom x y :=
  ⟨arrow, source, target⟩

/-- The underlying arrow of `ofArrow` is the supplied arrow. -/
theorem ofArrow_arrow {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {x y : ofOver T ⟶ G.U.left}
    (arrow : ofOver T ⟶ G.R.left) (source : arrow ≫ G.s.left = x)
    (target : arrow ≫ G.t.left = y) :
    (ofArrow arrow source target).arrow = arrow := sorry

/-- The endpoint equations of a morphism constructed by `ofArrow`. -/
theorem ofArrow_spec {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {x y : ofOver T ⟶ G.U.left}
    (arrow : ofOver T ⟶ G.R.left) (source : arrow ≫ G.s.left = x)
    (target : arrow ≫ G.t.left = y) :
    (ofArrow arrow source target).arrow ≫ G.s.left = x ∧
      (ofArrow arrow source target).arrow ≫ G.t.left = y := sorry

/-- Morphisms of scheme-valued points with the same underlying arrow are equal. -/
theorem ext {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : ofOver T ⟶ G.U.left} {f g : G.SpacePointHom x y}
    (h : f.arrow = g.arrow) : f = g := sorry

/-- The endpoint equations for the identity morphism of a scheme-valued point. -/
theorem id_endpoints {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} (x : ofOver T ⟶ G.U.left) :
    (x ≫ G.e.left) ≫ G.s.left = x ∧ (x ≫ G.e.left) ≫ G.t.left = x := sorry

/-- The two lifted arrows used to define a composite have the same base map. -/
theorem compArrow_over {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S}
    {x y z : ofOver T ⟶ G.U.left} (f : G.SpacePointHom x y)
    (g : G.SpacePointHom y z) : g.arrow ≫ G.R.hom = f.arrow ≫ G.R.hom := sorry

/-- The lifted arrows used to define a composite are composable in the groupoid over `B`. -/
theorem compArrow_compatible {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S}
    {x y z : ofOver T ⟶ G.U.left} (f : G.SpacePointHom x y)
    (g : G.SpacePointHom y z) :
    (Over.homMk g.arrow (compArrow_over f g) :
      Over.mk (f.arrow ≫ G.R.hom) ⟶ G.R) ≫ G.s =
      (Over.homMk f.arrow rfl : Over.mk (f.arrow ≫ G.R.hom) ⟶ G.R) ≫ G.t := sorry

/-- The composite arrow of two composable scheme-valued morphisms. -/
def compArrow {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y z : ofOver T ⟶ G.U.left} (f : G.SpacePointHom x y)
    (g : G.SpacePointHom y z) : ofOver T ⟶ G.R.left :=
  let later : Over.mk (f.arrow ≫ G.R.hom) ⟶ G.R :=
    Over.homMk g.arrow (compArrow_over f g)
  let earlier : Over.mk (f.arrow ≫ G.R.hom) ⟶ G.R := Over.homMk f.arrow rfl
  (G.compose later earlier (compArrow_compatible f g)).left

/-- The endpoint equations for the composite of two scheme-valued morphisms. -/
theorem comp_endpoints {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S}
    {x y z : ofOver T ⟶ G.U.left} (f : G.SpacePointHom x y)
    (g : G.SpacePointHom y z) :
    compArrow f g ≫ G.s.left = x ∧ compArrow f g ≫ G.t.left = z := sorry

/-- The identity morphism of a scheme-valued point is induced by the identity-arrow map. -/
def id {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} (x : ofOver T ⟶ G.U.left) : G.SpacePointHom x x where
  arrow := x ≫ G.e.left
  source := (id_endpoints (G := G) x).1
  target := (id_endpoints (G := G) x).2

/-- The composite of two morphisms of scheme-valued points. -/
def comp {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y z : ofOver T ⟶ G.U.left} (f : G.SpacePointHom x y)
    (g : G.SpacePointHom y z) : G.SpacePointHom x z where
  arrow := compArrow f g
  source := (comp_endpoints f g).1
  target := (comp_endpoints f g).2

/-- The endpoint equations for the inverse of a scheme-valued morphism. -/
theorem inv_endpoints {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S}
    {x y : ofOver T ⟶ G.U.left} (f : G.SpacePointHom x y) :
    (f.arrow ≫ G.i.left) ≫ G.s.left = y ∧
      (f.arrow ≫ G.i.left) ≫ G.t.left = x := sorry

/-- The inverse of a morphism of scheme-valued points is induced by the inverse-arrow map. -/
def inv {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : ofOver T ⟶ G.U.left} (f : G.SpacePointHom x y) :
    G.SpacePointHom y x where
  arrow := f.arrow ≫ G.i.left
  source := (inv_endpoints f).1
  target := (inv_endpoints f).2

/-- The identity law for composition of scheme-valued morphisms. -/
theorem id_comp {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : ofOver T ⟶ G.U.left} (f : G.SpacePointHom x y) :
    comp (id x) f = f := sorry

/-- The right identity law for composition of scheme-valued morphisms. -/
theorem comp_id {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : ofOver T ⟶ G.U.left} (f : G.SpacePointHom x y) :
    comp f (id y) = f := sorry

/-- Associativity of composition of scheme-valued morphisms. -/
theorem assoc {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y z w : ofOver T ⟶ G.U.left} (f : G.SpacePointHom x y)
    (g : G.SpacePointHom y z) (h : G.SpacePointHom z w) :
    comp (comp f g) h = comp f (comp g h) := sorry

/-- Composition with an inverse on the left yields the identity. -/
theorem inv_comp {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : ofOver T ⟶ G.U.left} (f : G.SpacePointHom x y) :
    comp (inv f) f = id y := sorry

/-- Composition with an inverse on the right yields the identity. -/
theorem comp_inv {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : ofOver T ⟶ G.U.left} (f : G.SpacePointHom x y) :
    comp f (inv f) = id x := sorry

/-- The endpoint equations for restriction of a pointwise morphism. -/
theorem restrict_endpoints {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T T' : Over S}
    {x y : ofOver T' ⟶ G.U.left} (f : T ⟶ T') (p : G.SpacePointHom x y) :
    (yoneda.map f ≫ p.arrow) ≫ G.s.left = yoneda.map f ≫ x ∧
      (yoneda.map f ≫ p.arrow) ≫ G.t.left = yoneda.map f ≫ y := sorry

/-- Restriction of a pointwise morphism along a morphism of schemes over `S`. -/
def restrict {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T T' : Over S} {x y : ofOver T' ⟶ G.U.left} (f : T ⟶ T')
    (p : G.SpacePointHom x y) :
    G.SpacePointHom (yoneda.map f ≫ x) (yoneda.map f ≫ y) where
  arrow := yoneda.map f ≫ p.arrow
  source := (restrict_endpoints f p).1
  target := (restrict_endpoints f p).2

/-- Restriction of a pointwise identity is the identity of the restricted point. -/
theorem restrict_id {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T T' : Over S} (f : T ⟶ T')
    (x : ofOver T' ⟶ G.U.left) : restrict f (id x) = id (yoneda.map f ≫ x) := sorry

/-- Restriction of a pointwise composite is the composite of the restrictions. -/
theorem restrict_comp {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T T' : Over S} (f : T ⟶ T')
    {x y z : ofOver T' ⟶ G.U.left} (p : G.SpacePointHom x y)
    (q : G.SpacePointHom y z) :
    restrict f (comp p q) = comp (restrict f p) (restrict f q) := sorry

end SpacePointHom

/-- The explicit groupoid structure on the scheme-valued points of a groupoid in algebraic spaces. -/
@[reducible]
def spacePointGroupoid {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (T : Over S) :
    CategoryTheory.Groupoid.{u + 1, u + 1} (ofOver T ⟶ G.U.left) where
  Hom := fun x y ↦ G.SpacePointHom x y
  id := fun x ↦ SpacePointHom.id x
  comp := fun f g ↦ SpacePointHom.comp f g
  id_comp := fun f ↦ SpacePointHom.id_comp f
  comp_id := fun f ↦ SpacePointHom.comp_id f
  assoc := fun f g h ↦ SpacePointHom.assoc f g h
  inv := fun f ↦ SpacePointHom.inv f
  inv_comp := fun f ↦ SpacePointHom.inv_comp f
  comp_inv := fun f ↦ SpacePointHom.comp_inv f

/-- The bundled groupoid of scheme-valued points. -/
def spacePoints {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (T : Over S) : Grpd.{u + 1, u + 1} :=
  ⟨ofOver T ⟶ G.U.left, G.spacePointGroupoid T⟩

/-- The objects of `spacePoints G T` are the morphisms `ofOver T ⟶ G.U.left`. -/
theorem spacePoints_obj {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (T : Over S) :
    (G.spacePoints T : Type (u + 1)) = (ofOver T ⟶ G.U.left) := sorry

/-- Restriction of scheme-valued point groupoids along a morphism over `S`. -/
def spacePointsMap {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' : Over S} (f : T ⟶ T') :
    G.spacePoints T' ⟶ G.spacePoints T where
  obj x := yoneda.map f ≫ x
  map p := SpacePointHom.restrict f p
  map_id x := SpacePointHom.restrict_id f x
  map_comp p q := SpacePointHom.restrict_comp f p q

/-- Restriction of point groupoids along an identity is the identity morphism. -/
theorem spacePointsMap_id {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} :
    spacePointsMap G (𝟙 T) = 𝟙 (G.spacePoints T) := sorry

/-- Restriction of point groupoids respects composition of morphisms over `S`. -/
theorem spacePointsMap_comp {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T T' T'' : Over S} (f : T ⟶ T') (g : T' ⟶ T'') :
    spacePointsMap G (f ≫ g) = spacePointsMap G g ≫ spacePointsMap G f := sorry

/-- Scheme-valued points form a contravariant functor to bundled groupoids. -/
def points {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (Over S)ᵒᵖ ⥤ Grpd.{u + 1, u + 1} where
  obj T := G.spacePoints T.unop
  map f := spacePointsMap G f.unop
  map_id T := spacePointsMap_id (G := G) (T := T.unop)
  map_comp f g := spacePointsMap_comp g.unop f.unop

/-- The objects of the point groupoid over `T` are the morphisms `ofOver T ⟶ G.U.left`. -/
theorem points_obj {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (T : Over S) :
    (G.points.obj (op T) : Type (u + 1)) = (ofOver T ⟶ G.U.left) := sorry

/-- Pullback of points along a morphism is given by precomposition with its Yoneda image. -/
theorem points_map_obj {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    (x : ofOver T.unop ⟶ G.U.left) :
    (G.points.map f).obj x = yoneda.map f.unop ≫ x := sorry

/-- Pullback of a pointwise arrow along a base morphism is given by precomposition with its
Yoneda image. -/
theorem points_map_arrow {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    {x y : ofOver T.unop ⟶ G.U.left} (p : G.SpacePointHom x y) :
    ((G.points.map f).map p).arrow = yoneda.map f.unop ≫ p.arrow := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

end
