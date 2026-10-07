module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Topology.Defs.Induced
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# Quotient maps on points of algebraic spaces

A morphism of algebraic spaces is a quotient map on points when the induced map
of underlying point spaces is a quotient map for every pair of canonical
topologies. The canonical topology on `Points` is characterized rather than
constructed, so competing topologies remain explicit parameters.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The map on points induced by `f` is a quotient map with respect to the given
topologies on the source and target point spaces. -/
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
        Function.Surjective (Points.map f) :=
  sorry

/-- The morphism property of inducing a quotient map on canonical point spaces. -/
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
  sorry

namespace pointsIsQuotientMap

/-- A morphism has the `pointsIsQuotientMap` property as soon as the induced map
on points is a quotient map for every pair of canonical topologies. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
      IsPointsTopology X τX → IsPointsTopology Y τY → isQuotientMapOnPoints τX τY f) :
    pointsIsQuotientMap f :=
  sorry

/-- A morphism with the `pointsIsQuotientMap` property induces a quotient map on
points for any pair of canonical topologies. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : pointsIsQuotientMap f) {τX : TopologicalSpace (Points X)}
    {τY : TopologicalSpace (Points Y)} (hX : IsPointsTopology X τX)
    (hY : IsPointsTopology Y τY) :
    isQuotientMapOnPoints τX τY f :=
  sorry

/-- The base-change projection `pullback.snd f g` of a morphism that is
universally a quotient map on points is a quotient map on points. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : universally pointsIsQuotientMap f) (g : Z ⟶ Y) [HasPullback f g] :
    pointsIsQuotientMap (pullback.snd f g) :=
  sorry

end pointsIsQuotientMap

/-- A morphism is universally a quotient map on points if and only if every base
change, expressed by an `IsPullback` square, is a quotient map on points. -/
theorem universally_pointsIsQuotientMap_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    universally pointsIsQuotientMap f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → pointsIsQuotientMap pZ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
