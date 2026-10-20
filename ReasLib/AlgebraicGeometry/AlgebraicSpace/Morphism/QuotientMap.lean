module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism

/-!
# Quotient maps on algebraic-space points
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The map on points of a morphism is a quotient map for the specified source
and target topologies. -/
def isQuotientMapOnPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @Topology.IsQuotientMap (Points X) (Points Y) τX τY (Points.map f)

/-- Being a quotient map on points means the induced map is coinducing and
surjective for the given topologies. -/
theorem isQuotientMapOnPoints_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) :
    isQuotientMapOnPoints τX τY f ↔
      @Topology.IsCoinducing (Points X) (Points Y) τX τY (Points.map f) ∧
        Function.Surjective (Points.map f) := by
  exact ⟨fun h ↦ ⟨h.isCoinducing, h.surjective⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- A morphism induces a quotient map on points for every pair of canonical
topologies on its source and target. -/
def pointsIsQuotientMap {S : Scheme.{u}} : MorphismProperty (AlgebraicSpace S) :=
  fun {X Y} f ↦
    ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
      IsPointsTopology X τX → IsPointsTopology Y τY → isQuotientMapOnPoints τX τY f

/-- A morphism induces a quotient map on points if it does so for every pair of
canonical topologies on the source and target. -/
theorem pointsIsQuotientMap_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    pointsIsQuotientMap f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isQuotientMapOnPoints τX τY f :=
  Iff.rfl

namespace pointsIsQuotientMap

/-- A morphism induces a quotient map on points whenever it does so for every
pair of canonical topologies. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
      IsPointsTopology X τX → IsPointsTopology Y τY → isQuotientMapOnPoints τX τY f) :
    pointsIsQuotientMap f :=
  hf

/-- A morphism inducing a quotient map on points does so for any pair of
canonical topologies. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : pointsIsQuotientMap f) {τX : TopologicalSpace (Points X)}
    {τY : TopologicalSpace (Points Y)} (hX : IsPointsTopology X τX)
    (hY : IsPointsTopology Y τY) :
    isQuotientMapOnPoints τX τY f :=
  hf τX τY hX hY

/-- The base-change projection of a morphism that is universally a quotient map
on points is a quotient map on points. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : universally pointsIsQuotientMap f) (g : Z ⟶ Y) [HasPullback f g] :
    pointsIsQuotientMap (pullback.snd f g) :=
  hf (pullback.fst f g) g (pullback.snd f g) (IsPullback.of_hasPullback f g).flip

end pointsIsQuotientMap

/-- A morphism is universally a quotient map on points if and only if every base
change, expressed by a pullback square, is a quotient map on points. -/
theorem universally_pointsIsQuotientMap_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    universally pointsIsQuotientMap f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → pointsIsQuotientMap pZ := by
  constructor
  · intro hf Z P g pZ pX h
    exact hf pX g pZ h
  · intro hf P Z pX g pZ h
    exact hf h

end AlgebraicGeometry.AlgebraicSpace
