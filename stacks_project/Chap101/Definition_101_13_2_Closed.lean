/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap100.Lemma_100_4_3_Comparison
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty

/-!
# Closed morphisms of algebraic stacks

A morphism of algebraic stacks is closed when it induces a closed map on
underlying point spaces, and universally closed when every 2-fibre-product
base change is closed. The canonical topology on `Points` is characterized
rather than constructed, so competing topologies remain explicit parameters.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Points

/-- The map on points induced by a morphism `p : GroupoidsOver.slice U ⟶ X` from a
scheme over `S`. It sends a point `x` of `U` to the class of the residue-field
point of `x`, postcomposed with `p`. -/
def mapOfSlice {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) : U.left → Points X :=
  fun x ↦
    mk ((FieldValuedPoint.of (U.left.residueField x : Type u)
        (U.left.fromSpecResidueField x ≫ U.hom)
        (overMap (Over.homMk (U.left.fromSpecResidueField x)))).map p)

/-- `mapOfSlice p x` is the class of the residue-field point of `x`, postcomposed
with `p`. -/
theorem mapOfSlice_apply {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {U : Over S} (p : GroupoidsOver.slice U ⟶ X)
    (x : U.left) :
    mapOfSlice p x =
      mk ((FieldValuedPoint.of (U.left.residueField x : Type u)
          (U.left.fromSpecResidueField x ≫ U.hom)
          (overMap (Over.homMk (U.left.fromSpecResidueField x)))).map p) :=
  sorry

/-- The slice-to-points map is natural in morphisms of algebraic stacks. -/
theorem map_mapOfSlice {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) (f : X ⟶ Y) (x : U.left) :
    map f (mapOfSlice p x) = mapOfSlice (p ≫ f) x :=
  sorry

end Points

/-- A topology on the points of an algebraic stack is the canonical one when every
smooth surjective scheme atlas is a quotient map onto those points. -/
def IsPointsTopology {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (τ : TopologicalSpace (Points X)) : Prop :=
  ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
    Groupoids.Hom.Smooth p → Groupoids.Hom.Surjective p →
      @Topology.IsQuotientMap U.left (Points X)
        (inferInstance : TopologicalSpace U.left) τ (Points.mapOfSlice p)

/-- A topology is canonical on points of an algebraic stack exactly when every
smooth surjective scheme atlas is a quotient map. -/
theorem isPointsTopology_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (τ : TopologicalSpace (Points X)) :
    IsPointsTopology X τ ↔
      ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p → Groupoids.Hom.Surjective p →
          @Topology.IsQuotientMap U.left (Points X)
            (inferInstance : TopologicalSpace U.left) τ (Points.mapOfSlice p) :=
  sorry

/-- A canonical topology on points makes every smooth surjective scheme atlas a
quotient map. -/
theorem isPointsTopology_isQuotientMap {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) {U : Over S} {p : GroupoidsOver.slice U ⟶ X}
    (hp_smooth : Groupoids.Hom.Smooth p) (hp_surj : Groupoids.Hom.Surjective p) :
    @Topology.IsQuotientMap U.left (Points X)
      (inferInstance : TopologicalSpace U.left) τ (Points.mapOfSlice p) :=
  sorry

/-- Canonical topologies on the points of an algebraic stack are unique. -/
theorem isPointsTopology_unique {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {τ τ' : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (hτ' : IsPointsTopology X τ') : τ = τ' :=
  sorry

/-- The map on points induced by `f` is a closed map with respect to the given
topologies on the source and target point spaces. -/
def isClosedMapOnPoints {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @IsClosedMap (Points X) (Points Y) τX τY (Points.map f)

/-- Being a closed map on points means closed sets in the source point space have
closed images in the target. -/
theorem isClosedMapOnPoints_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) :
    isClosedMapOnPoints τX τY f ↔
      ∀ (U : Set (Points X)),
        @IsClosed (Points X) τX U →
          @IsClosed (Points Y) τY (Points.map f '' U) :=
  sorry

/-- A morphism of algebraic stacks induces a closed map on canonical point
spaces. -/
def pointsIsClosedMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
    IsPointsTopology X τX → IsPointsTopology Y τY → isClosedMapOnPoints τX τY f

/-- A morphism induces a closed map on points if it does so for every pair of
canonical topologies on the source and target. -/
theorem pointsIsClosedMap_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    pointsIsClosedMap f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isClosedMapOnPoints τX τY f :=
  sorry

/-- A morphism of algebraic stacks is closed if the induced map on underlying
point spaces is a closed map. -/
@[mk_iff]
class Closed {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The map on points induced by `f` is closed for every pair of canonical
  topologies. -/
  isClosedMap : pointsIsClosedMap f

namespace Closed

/-- The identity morphism of an algebraic stack is closed. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Closed (𝟙 X) :=
  sorry

/-- A closed morphism induces a closed map on points for any pair of canonical
topologies. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [Closed f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    isClosedMapOnPoints τX τY f :=
  sorry

/-- A morphism is closed as soon as it induces a closed map on canonical point
spaces. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : pointsIsClosedMap f) : Closed f :=
  sorry

end Closed

/-- A morphism of algebraic stacks is universally closed if every 2-fibre-product
base change induces a closed map on underlying point spaces. -/
@[mk_iff]
class UniversallyClosed {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Every 2-fibre-product base change of `f` is a closed morphism. -/
  closed_baseChange {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
      {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g) :
      (Points.cone iso).IsBilimit → Closed snd

namespace UniversallyClosed

/-- The identity morphism of an algebraic stack is universally closed. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    UniversallyClosed (𝟙 X) :=
  sorry

/-- A universally closed morphism has closed 2-fibre-product base changes. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [UniversallyClosed f]
    {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
    {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g)
    (h : (Points.cone iso).IsBilimit) : Closed snd :=
  sorry

/-- Every 2-fibre-product projection `snd` of a universally closed morphism is
closed. -/
theorem isClosed_of_isBilimit {S : Scheme.{u}} {X Y Z P : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack P]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z}
    [UniversallyClosed f] (iso : fst ≫ f ≅ snd ≫ g)
    (h : (Points.cone iso).IsBilimit) : Closed snd :=
  sorry

/-- The chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` of a universally closed
morphism `f : X ⟶ Y` is closed, once the apex is known to be an algebraic
stack. -/
theorem twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} (g : Z ⟶ Y) [UniversallyClosed f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end UniversallyClosed

/-- A universally closed morphism of algebraic stacks is closed. -/
instance instClosed_of_universallyClosed {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [UniversallyClosed f] : Closed f :=
  sorry

/-- Typeclass form of closedness of the chosen 2-fibre-product projection of a
universally closed morphism. -/
instance instClosed_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyClosed f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- A morphism of algebraic stacks is universally closed if and only if every
2-fibre-product base change, expressed by an `IsBilimit` square, is a closed
morphism. -/
theorem universallyClosed_iff_isClosed_of_isBilimit {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    UniversallyClosed f ↔
      ∀ {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
        {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z}
        (iso : fst ≫ f ≅ snd ≫ g),
        (Points.cone iso).IsBilimit → Closed snd :=
  sorry

/-- A morphism of algebraic stacks is universally closed if and only if every
chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` is closed. -/
theorem universallyClosed_iff_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    UniversallyClosed f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack

