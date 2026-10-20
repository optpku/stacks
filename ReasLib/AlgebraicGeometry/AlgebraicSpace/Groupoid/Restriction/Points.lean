/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.InducedCategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction

/-!
# Groupoids of points of a restricted groupoid

The point groupoid of a restriction is equivalent to the induced point category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace


/-- The endpoints of an original pointwise arrow over the image of `U'` give the second
projection needed to lift that arrow to the restricted arrow space. -/
theorem liftPointArrow_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B} {x y : Over.mk σ ⟶ U'}
    (p : G.PointHom σ (x ≫ g) (y ≫ g)) :
    p.arrow ≫ G.toPreRelation.hom = prod.lift y x ≫ prod.map g g := sorry

/-- Lift an original pointwise arrow whose endpoints lie in `U'` to the restricted arrow
space. -/
def liftPointArrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B} {x y : Over.mk σ ⟶ U'}
    (p : G.PointHom σ (x ≫ g) (y ≫ g)) :
    Over.mk σ ⟶ (G.toPreRelation.pullback g).left :=
  Limits.pullback.lift p.arrow (prod.lift y x) (liftPointArrow_condition G g p)

/-- The lifted point arrow has the prescribed source. -/
theorem liftPoint_source {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B} {x y : Over.mk σ ⟶ U'}
    (p : G.PointHom σ (x ≫ g) (y ≫ g)) :
    liftPointArrow G g p ≫ (pullback G g).s = x := sorry

/-- The lifted point arrow has the prescribed target. -/
theorem liftPoint_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B} {x y : Over.mk σ ⟶ U'}
    (p : G.PointHom σ (x ≫ g) (y ≫ g)) :
    liftPointArrow G g p ≫ (pullback G g).t = y := sorry

/-- Lift an arrow of the induced category to the restricted point groupoid. -/
def liftPoint {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B} {x y : Over.mk σ ⟶ U'}
    (p : G.PointHom σ (x ≫ g) (y ≫ g)) : (pullback G g).PointHom σ x y where
  arrow := liftPointArrow G g p
  source := liftPoint_source G g p
  target := liftPoint_target G g p

/-- Mapping a lifted pointwise arrow recovers its original underlying arrow. -/
theorem map_liftPoint_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B} {x y : Over.mk σ ⟶ U'}
    (p : G.PointHom σ (x ≫ g) (y ≫ g)) :
    (((pullbackHom G g).mapPoints σ).map (liftPoint G g p)).arrow = p.arrow := sorry

/-- The object map on `T`-points induced by the morphism `g : U' ⟶ G.U`. -/
def restrictionObjectMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    (Over.mk σ ⟶ U') → G.groupoidPoints σ :=
  fun x ↦ x ≫ g

/-- The restriction object map is postcomposition with `g`. -/
theorem restrictionObjectMap_apply {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) (x : Over.mk σ ⟶ U') :
    restrictionObjectMap G g σ x = x ≫ g := sorry

/-- Mapping identities to the induced point category preserves identity arrows. -/
theorem pointsToInducedFunctor_map_id {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B)
    (x : (pullback G g).groupoidPoints σ) :
    InducedCategory.homMk (((pullbackHom G g).mapPoints σ).map (𝟙 x)) =
      InducedCategory.homMk (PointHom.id (G := G) σ (x ≫ g)) := sorry

/-- Mapping composites to the induced point category preserves composition. -/
theorem pointsToInducedFunctor_map_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B)
    {x y z : (pullback G g).groupoidPoints σ} (p : x ⟶ y) (q : y ⟶ z) :
    InducedCategory.homMk (((pullbackHom G g).mapPoints σ).map (p ≫ q)) =
      InducedCategory.homMk (((pullbackHom G g).mapPoints σ).map p) ≫
        InducedCategory.homMk (((pullbackHom G g).mapPoints σ).map q) := sorry

/-- The functor from restricted points to the category induced from the original point
groupoid. -/
def pointsToInducedFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    (pullback G g).groupoidPoints σ ⥤
      InducedCategory (G.groupoidPoints σ) (fun x : Over.mk σ ⟶ U' ↦ x ≫ g) where
  obj x := x
  map p := InducedCategory.homMk (((pullbackHom G g).mapPoints σ).map p)
  map_id := pointsToInducedFunctor_map_id G g σ
  map_comp := pointsToInducedFunctor_map_comp G g σ

/-- Lifting an identity from the induced point category preserves identity arrows. -/
theorem pointsFromInducedFunctor_map_id {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B)
    (x : InducedCategory (G.groupoidPoints σ) (fun z : Over.mk σ ⟶ U' ↦ z ≫ g)) :
    liftPoint G g ((𝟙 x : x ⟶ x).hom) =
      PointHom.id (G := pullback G g) σ x := sorry

/-- Lifting a composite from the induced point category preserves composition. -/
theorem pointsFromInducedFunctor_map_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B)
    {x y z : InducedCategory (G.groupoidPoints σ) (fun v : Over.mk σ ⟶ U' ↦ v ≫ g)}
    (p : x ⟶ y) (q : y ⟶ z) :
    liftPoint G g (p ≫ q).hom =
      PointHom.comp (liftPoint G g p.hom) (liftPoint G g q.hom) := sorry

/-- The functor from the induced category back to the restricted point groupoid. -/
def pointsFromInducedFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    InducedCategory (G.groupoidPoints σ) (fun x : Over.mk σ ⟶ U' ↦ x ≫ g) ⥤
      (pullback G g).groupoidPoints σ where
  obj x := x
  map p := liftPoint G g p.hom
  map_id := pointsFromInducedFunctor_map_id G g σ
  map_comp := pointsFromInducedFunctor_map_comp G g σ

/-- Naturality of the identity components for the unit of the pointwise restriction
equivalence. -/
theorem pointsPullbackUnit_naturality {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B)
    {x y : (pullback G g).groupoidPoints σ} (p : x ⟶ y) :
    (𝟭 ((pullback G g).groupoidPoints σ)).map p ≫ (Iso.refl y).hom =
      (Iso.refl x).hom ≫
        (pointsToInducedFunctor G g σ ⋙ pointsFromInducedFunctor G g σ).map p := sorry

/-- The unit isomorphism for the pointwise restriction equivalence. -/
def pointsPullbackUnitIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    𝟭 ((pullback G g).groupoidPoints σ) ≅
      pointsToInducedFunctor G g σ ⋙ pointsFromInducedFunctor G g σ :=
  NatIso.ofComponents (fun x ↦ Iso.refl x) (pointsPullbackUnit_naturality G g σ)

/-- Naturality of the identity components for the counit of the pointwise restriction
equivalence. -/
theorem pointsPullbackCounit_naturality {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B)
    {x y : InducedCategory (G.groupoidPoints σ) (fun z : Over.mk σ ⟶ U' ↦ z ≫ g)}
    (p : x ⟶ y) :
    (pointsFromInducedFunctor G g σ ⋙ pointsToInducedFunctor G g σ).map p ≫
        (Iso.refl y).hom =
      (Iso.refl x).hom ≫
        (𝟭 (InducedCategory (G.groupoidPoints σ)
          (fun z : Over.mk σ ⟶ U' ↦ z ≫ g))).map p := sorry

/-- The counit isomorphism for the pointwise restriction equivalence. -/
def pointsPullbackCounitIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    pointsFromInducedFunctor G g σ ⋙ pointsToInducedFunctor G g σ ≅
      𝟭 (InducedCategory (G.groupoidPoints σ) (fun x : Over.mk σ ⟶ U' ↦ x ≫ g)) :=
  NatIso.ofComponents (fun x ↦ Iso.refl x) (pointsPullbackCounit_naturality G g σ)

/-- The identity unit and counit satisfy the triangle identity. -/
theorem pointsPullbackTriangle {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B)
    (x : (pullback G g).groupoidPoints σ) :
    (pointsToInducedFunctor G g σ).map ((pointsPullbackUnitIso G g σ).hom.app x) ≫
        (pointsPullbackCounitIso G g σ).hom.app
          ((pointsToInducedFunctor G g σ).obj x) =
      𝟙 ((pointsToInducedFunctor G g σ).obj x) := sorry

/-- The groupoid of `T`-points of a restriction is canonically equivalent to the category
induced from the original point groupoid along `x ↦ x ≫ g`. -/
def pointsPullbackEquivalence {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    (pullback G g).groupoidPoints σ ≌
      InducedCategory (G.groupoidPoints σ) (fun x : Over.mk σ ⟶ U' ↦ x ≫ g) where
  functor := pointsToInducedFunctor G g σ
  inverse := pointsFromInducedFunctor G g σ
  unitIso := pointsPullbackUnitIso G g σ
  counitIso := pointsPullbackCounitIso G g σ
  functor_unitIso_comp := pointsPullbackTriangle G g σ

/-- The pointwise restriction equivalence followed by the induced functor is the functor on
points defined by the canonical groupoid morphism. -/
theorem pointsPullbackEquivalence_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    (pointsPullbackEquivalence G g σ).functor ⋙
        CategoryTheory.inducedFunctor (restrictionObjectMap G g σ) =
      (pullbackHom G g).mapPoints σ := sorry

/-- The point groupoid restricted along an arbitrary algebraic-space morphism agrees with
the induced category of the original point groupoid. -/
def pointsPullbackAlongEquivalence {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : AlgebraicSpace S} (g : U' ⟶ G.U.left)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    (pullbackAlong G g).groupoidPoints σ ≌
      InducedCategory (G.groupoidPoints σ)
        (fun x : Over.mk σ ⟶ Over.mk (g ≫ G.U.hom) ↦
          x ≫ (Over.homMk g rfl : Over.mk (g ≫ G.U.hom) ⟶ G.U)) :=
  pointsPullbackEquivalence G (Over.homMk g rfl : Over.mk (g ≫ G.U.hom) ⟶ G.U) σ

/-- The pointwise equivalence for a raw map agrees with the canonical projection on points. -/
theorem pointsPullbackAlongEquivalence_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : AlgebraicSpace S} (g : U' ⟶ G.U.left)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    (pointsPullbackAlongEquivalence G g σ).functor ⋙
        CategoryTheory.inducedFunctor
          (restrictionObjectMap G
            (Over.homMk g rfl : Over.mk (g ≫ G.U.hom) ⟶ G.U) σ) =
      (pullbackAlongHom G g).mapPoints σ :=
  pointsPullbackEquivalence_comp G
    (Over.homMk g rfl : Over.mk (g ≫ G.U.hom) ⟶ G.U) σ
end AlgebraicGeometry.GroupoidAlgebraicSpace
