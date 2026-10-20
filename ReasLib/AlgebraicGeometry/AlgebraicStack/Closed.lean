module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Closed morphisms of algebraic stacks

A morphism is closed when its map on canonical point spaces is closed, and
universally closed when every algebraic-stack base change is closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

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
  isClosedMapOnPoints (Points.topology X) (Points.topology Y) f

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
  /-- The map on points induced by `f` is closed in the canonical topologies. -/
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

end Closed

/-- A morphism of algebraic stacks is universally closed if every 2-fibre-product
base change induces a closed map on underlying point spaces. -/
@[mk_iff]
class UniversallyClosed {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Every 2-fibre-product base change of `f` is a closed morphism. -/
  closed_baseChange {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
      {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g) :
      (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Closed snd

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
    (h : (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit) : Closed snd :=
  sorry

/-- The chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` of a universally closed
morphism `f : X ⟶ Y` is closed. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} (g : Z ⟶ Y) [UniversallyClosed f] :
    Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end UniversallyClosed

/-- A universally closed morphism of algebraic stacks is closed. -/
instance instClosed_of_universallyClosed {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [UniversallyClosed f] : Closed f :=
  sorry

/-- A morphism of algebraic stacks is universally closed if and only if every
chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` is closed. -/
theorem universallyClosed_iff_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    UniversallyClosed f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y),
        Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack

