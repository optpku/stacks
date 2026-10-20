/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Functoriality of scheme-valued point groupoids

A morphism of groupoids in algebraic spaces induces a natural transformation
of their groupoid-valued functors of scheme points by postcomposition.
-/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}

private theorem pointsMapArrow_endpoints (f : Hom G H) {T : Over S}
    {x y : ofOver T ⟶ G.U.left} (p : G.SpacePointHom x y) :
    (p.arrow ≫ f.arrow.left) ≫ H.s.left = x ≫ f.obj.left ∧
      (p.arrow ≫ f.arrow.left) ≫ H.t.left = y ≫ f.obj.left := sorry

private def pointsMapArrow (f : Hom G H) {T : Over S}
    {x y : ofOver T ⟶ G.U.left} (p : G.SpacePointHom x y) :
    H.SpacePointHom (x ≫ f.obj.left) (y ≫ f.obj.left) where
  arrow := p.arrow ≫ f.arrow.left
  source := (pointsMapArrow_endpoints f p).1
  target := (pointsMapArrow_endpoints f p).2

private theorem pointsMapApp_map_id (f : Hom G H) (T : Over S)
    (x : ofOver T ⟶ G.U.left) :
    pointsMapArrow f (SpacePointHom.id x) = SpacePointHom.id (x ≫ f.obj.left) := sorry

private theorem pointsMapApp_map_comp (f : Hom G H) (T : Over S)
    {x y z : ofOver T ⟶ G.U.left} (p : G.SpacePointHom x y)
    (q : G.SpacePointHom y z) :
    pointsMapArrow f (SpacePointHom.comp p q) =
      SpacePointHom.comp (pointsMapArrow f p) (pointsMapArrow f q) := sorry

private def pointsMapApp (f : Hom G H) (T : Over S) :
    G.spacePoints T ⟶ H.spacePoints T where
  obj x := x ≫ f.obj.left
  map p := pointsMapArrow f p
  map_id x := pointsMapApp_map_id f T x
  map_comp p q := pointsMapApp_map_comp f T p q

private theorem pointsMapApp_naturality (f : Hom G H)
    {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    G.points.map g ≫ pointsMapApp f T'.unop =
      pointsMapApp f T.unop ≫ H.points.map g := sorry

/-- A morphism of groupoids in algebraic spaces induces a natural transformation of
scheme-valued point groupoids by postcomposition with its object and arrow maps. -/
def pointsMap (f : Hom G H) : G.points ⟶ H.points where
  app T := pointsMapApp f T.unop
  naturality := fun _ _ g ↦ pointsMapApp_naturality f g

/-- The induced transformation of point groupoids postcomposes objects with the object map. -/
theorem pointsMap_obj (f : Hom G H) (T : Over S) (x : ofOver T ⟶ G.U.left) :
    (f.pointsMap.app (op T)).obj x = x ≫ f.obj.left := rfl

/-- The induced transformation of point groupoids postcomposes arrows with the arrow map. -/
theorem pointsMap_map_arrow (f : Hom G H) (T : Over S)
    {x y : ofOver T ⟶ G.U.left} (p : G.SpacePointHom x y) :
    ((f.pointsMap.app (op T)).map p).arrow = p.arrow ≫ f.arrow.left := rfl

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
