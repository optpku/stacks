/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.InducedCategory
public import stacks_project.Chap78.Lemma_78_17_1_Restriction

/-!
# Points of a restricted groupoid in algebraic spaces

This module identifies the groupoid of scheme-valued points of a restricted groupoid in
algebraic spaces with the induced category obtained by restricting the original point
groupoid along the object map.
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

/-- Lift an arrow of the induced category to the restricted point groupoid. -/
def liftPoint {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B} {x y : Over.mk σ ⟶ U'}
    (p : G.PointHom σ (x ≫ g) (y ≫ g)) : (pullback G g).PointHom σ x y where
  arrow := liftPointArrow G g p
  source := sorry
  target := sorry

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

/-- The functor from restricted points to the category induced from the original point
groupoid. -/
def pointsToInducedFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    (pullback G g).groupoidPoints σ ⥤
      InducedCategory (G.groupoidPoints σ) (fun x : Over.mk σ ⟶ U' ↦ x ≫ g) where
  obj x := x
  map p := InducedCategory.homMk (((pullbackHom G g).mapPoints σ).map p)
  map_id := sorry
  map_comp := sorry

/-- The functor from the induced category back to the restricted point groupoid. -/
def pointsFromInducedFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    InducedCategory (G.groupoidPoints σ) (fun x : Over.mk σ ⟶ U' ↦ x ≫ g) ⥤
      (pullback G g).groupoidPoints σ where
  obj x := x
  map p := liftPoint G g p.hom
  map_id := sorry
  map_comp := sorry

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

end AlgebraicGeometry.GroupoidAlgebraicSpace
