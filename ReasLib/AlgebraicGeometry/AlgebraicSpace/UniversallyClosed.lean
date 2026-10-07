module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Topology.Defs.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism

/-!
# Closed morphisms of algebraic spaces

A morphism of algebraic spaces is closed when it induces a closed map on
underlying point spaces, and universally closed when every base change is closed.
The canonical topology on `Points` is characterized rather than constructed, so
competing topologies remain explicit parameters.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The map on points induced by `f` is a closed map with respect to the given
topologies on the source and target point spaces. -/
def isClosedMapOnPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @IsClosedMap (Points X) (Points Y) τX τY (Points.map f)

/-- Being a closed map on points means closed sets in the source point space have
closed images in the target. -/
theorem isClosedMapOnPoints_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) :
    isClosedMapOnPoints τX τY f ↔
      ∀ (U : Set (Points X)),
        @IsClosed (Points X) τX U → @IsClosed (Points Y) τY (Points.map f '' U) :=
  sorry

/-- The morphism property of inducing a closed map on canonical point spaces. -/
def pointsIsClosedMap {S : Scheme.{u}} : MorphismProperty (AlgebraicSpace S) :=
  fun {X Y} f ↦
    ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
      IsPointsTopology X τX → IsPointsTopology Y τY → isClosedMapOnPoints τX τY f

/-- A morphism induces a closed map on points if it does so for every pair of
canonical topologies on the source and target. -/
theorem pointsIsClosedMap_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    pointsIsClosedMap f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isClosedMapOnPoints τX τY f :=
  sorry

/-- A morphism of algebraic spaces is closed if the induced map on underlying
point spaces is a closed map. -/
@[mk_iff]
class Closed {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The map on points induced by `f` is closed for every pair of canonical
  topologies. -/
  isClosedMap : pointsIsClosedMap f

namespace Closed

/-- The identity morphism of an algebraic space is closed. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Closed (𝟙 X) := sorry

/-- A closed morphism induces a closed map on points for any pair of canonical
topologies. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [Closed f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    isClosedMapOnPoints τX τY f :=
  sorry

/-- A morphism is closed as soon as it induces a closed map on canonical point
spaces. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : pointsIsClosedMap f) : Closed f :=
  sorry

end Closed

/-- A morphism of algebraic spaces is universally closed if every base change
induces a closed map on underlying point spaces. -/
@[mk_iff]
class UniversallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every base change of `f` induces a closed map on points. -/
  universally_isClosedMap : universally pointsIsClosedMap f

namespace UniversallyClosed

/-- The identity morphism of an algebraic space is universally closed. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    UniversallyClosed (𝟙 X) :=
  sorry

/-- A universally closed morphism has the `universally pointsIsClosedMap`
morphism property. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [UniversallyClosed f] : universally pointsIsClosedMap f :=
  sorry

/-- Every base change of a universally closed morphism, expressed by an
`IsPullback` square, is a closed morphism. -/
theorem isClosed_of_isPullback {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X}
    [UniversallyClosed f] (h : IsPullback pZ pX g f) : Closed pZ :=
  sorry

/-- The base-change projection `pullback.snd f g : Z ×_Y X ⟶ Z` of a universally
closed morphism `f : X ⟶ Y` is closed. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : UniversallyClosed f) (g : Z ⟶ Y) [HasPullback f g] :
    Closed (pullback.snd f g) :=
  sorry

end UniversallyClosed

/-- A universally closed morphism of algebraic spaces is closed. -/
instance instClosed_of_universallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [UniversallyClosed f] : Closed f :=
  sorry

/-- Typeclass form of closedness of the chosen base-change projection of a
universally closed morphism. -/
instance instClosed_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyClosed f] [HasPullback f g] :
    Closed (pullback.snd f g) :=
  sorry

/-- A morphism of algebraic spaces is universally closed if and only if every
base change, expressed by an `IsPullback` square, is a closed morphism. -/
theorem universallyClosed_iff_isClosed_of_isPullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    UniversallyClosed f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → Closed pZ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
