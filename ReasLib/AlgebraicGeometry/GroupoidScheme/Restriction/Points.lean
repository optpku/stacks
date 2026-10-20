/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.InducedCategory
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction

/-!
# Points of a restricted groupoid scheme

This module identifies the groupoid of points of a restricted groupoid scheme with the induced
category obtained by restricting the original point groupoid along the object map.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The endpoints of an original pointwise arrow over the image of `U'` give the second
projection needed to lift that arrow to the restricted arrow scheme. -/
theorem liftPointArrow_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) {T : Over S} {x y : T ⟶ U'}
    (p : G.PointHom (x ≫ g) (y ≫ g)) :
    p.arrow ≫ G.toPreRelation.hom = prod.lift y x ≫ prod.map g g := sorry

/-- Lift an original pointwise arrow whose endpoints lie in `U'` to the restricted arrow
scheme. -/
def liftPointArrow {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) {T : Over S} {x y : T ⟶ U'}
    (p : G.PointHom (x ≫ g) (y ≫ g)) :
    T ⟶ (G.toPreRelation.pullback g).left :=
  Limits.pullback.lift p.arrow (prod.lift y x) (liftPointArrow_condition G g p)

/-- Lift an arrow of the induced category to the restricted point groupoid. -/
def liftPoint {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) {T : Over S} {x y : T ⟶ U'}
    (p : G.PointHom (x ≫ g) (y ≫ g)) : (pullback G g).PointHom x y where
  arrow := liftPointArrow G g p
  source := sorry
  target := sorry

/-- Mapping a lifted pointwise arrow recovers its original underlying arrow. -/
theorem map_liftPoint_arrow {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) {T : Over S} {x y : T ⟶ U'}
    (p : G.PointHom (x ≫ g) (y ≫ g)) :
    (((pullbackHom G g).mapPoints.app (Opposite.op T)).map (liftPoint G g p)).arrow =
      p.arrow := sorry

/-- The object map on `T`-points induced by the morphism `g : U' ⟶ G.U`. -/
def restrictionObjectMap {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (T : Over S) :
    (T ⟶ U') → G.groupoidPoints T :=
  fun x ↦ x ≫ g

/-- The restriction object map is postcomposition with `g`. -/
theorem restrictionObjectMap_apply {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (T : Over S) (x : T ⟶ U') :
    restrictionObjectMap G g T x = x ≫ g := sorry

/-- The functor from restricted points to the category induced from the original point
groupoid. -/
def pointsToInducedFunctor {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (T : Over S) :
    (pullback G g).groupoidPoints T ⥤
      InducedCategory (G.groupoidPoints T) (fun x : T ⟶ U' ↦ x ≫ g) where
  obj x := x
  map p := InducedCategory.homMk
    (((pullbackHom G g).mapPoints.app (Opposite.op T)).map p)
  map_id := sorry
  map_comp := sorry

/-- The functor from the induced category back to the restricted point groupoid. -/
def pointsFromInducedFunctor {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (T : Over S) :
    InducedCategory (G.groupoidPoints T) (fun x : T ⟶ U' ↦ x ≫ g) ⥤
      (pullback G g).groupoidPoints T where
  obj x := x
  map p := liftPoint G g p.hom
  map_id := sorry
  map_comp := sorry

/-- Naturality of the identity components for the unit of the pointwise restriction
equivalence. -/
theorem pointsPullbackUnit_naturality {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (T : Over S)
    {x y : (pullback G g).groupoidPoints T} (p : x ⟶ y) :
    (𝟭 ((pullback G g).groupoidPoints T)).map p ≫ (Iso.refl y).hom =
      (Iso.refl x).hom ≫
        (pointsToInducedFunctor G g T ⋙ pointsFromInducedFunctor G g T).map p := sorry

/-- The unit isomorphism for the pointwise restriction equivalence. -/
def pointsPullbackUnitIso {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (T : Over S) :
    𝟭 ((pullback G g).groupoidPoints T) ≅
      pointsToInducedFunctor G g T ⋙ pointsFromInducedFunctor G g T :=
  NatIso.ofComponents (fun x ↦ Iso.refl x) (pointsPullbackUnit_naturality G g T)

/-- Naturality of the identity components for the counit of the pointwise restriction
equivalence. -/
theorem pointsPullbackCounit_naturality {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (T : Over S)
    {x y : InducedCategory (G.groupoidPoints T) (fun z : T ⟶ U' ↦ z ≫ g)}
    (p : x ⟶ y) :
    (pointsFromInducedFunctor G g T ⋙ pointsToInducedFunctor G g T).map p ≫
        (Iso.refl y).hom =
      (Iso.refl x).hom ≫
        (𝟭 (InducedCategory (G.groupoidPoints T)
          (fun z : T ⟶ U' ↦ z ≫ g))).map p := sorry

/-- The counit isomorphism for the pointwise restriction equivalence. -/
def pointsPullbackCounitIso {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (T : Over S) :
    pointsFromInducedFunctor G g T ⋙ pointsToInducedFunctor G g T ≅
      𝟭 (InducedCategory (G.groupoidPoints T) (fun x : T ⟶ U' ↦ x ≫ g)) :=
  NatIso.ofComponents (fun x ↦ Iso.refl x) (pointsPullbackCounit_naturality G g T)

/-- The identity unit and counit satisfy the triangle identity. -/
theorem pointsPullbackTriangle {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (T : Over S)
    (x : (pullback G g).groupoidPoints T) :
    (pointsToInducedFunctor G g T).map ((pointsPullbackUnitIso G g T).hom.app x) ≫
        (pointsPullbackCounitIso G g T).hom.app ((pointsToInducedFunctor G g T).obj x) =
      𝟙 ((pointsToInducedFunctor G g T).obj x) := sorry

/-- The groupoid of `T`-points of a restriction is canonically equivalent to the category
induced from the original point groupoid along `x ↦ x ≫ g`. -/
def pointsPullbackEquivalence {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (T : Over S) :
    (pullback G g).groupoidPoints T ≌
      InducedCategory (G.groupoidPoints T) (fun x : T ⟶ U' ↦ x ≫ g) where
  functor := pointsToInducedFunctor G g T
  inverse := pointsFromInducedFunctor G g T
  unitIso := pointsPullbackUnitIso G g T
  counitIso := pointsPullbackCounitIso G g T
  functor_unitIso_comp := pointsPullbackTriangle G g T

/-- The pointwise restriction equivalence followed by the induced functor is the functor on
points defined by the canonical groupoid morphism. -/
theorem pointsPullbackEquivalence_comp {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (T : Over S) :
    (pointsPullbackEquivalence G g T).functor ⋙
        CategoryTheory.inducedFunctor (restrictionObjectMap G g T) =
      (pullbackHom G g).mapPoints.app (Opposite.op T) := sorry

end AlgebraicGeometry.GroupoidScheme

