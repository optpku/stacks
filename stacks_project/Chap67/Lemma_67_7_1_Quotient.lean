module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuotientMap

/-!
# Quotient maps on points of algebraic spaces

The quotient-map API is provided by its shared mathematical owner.
-/

open CategoryTheory AlgebraicGeometry Limits MorphismProperty
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.isQuotientMapOnPoints_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y),
    isQuotientMapOnPoints τX τY f ↔
      @Topology.IsCoinducing (Points X) (Points Y) τX τY (Points.map f) ∧
        Function.Surjective (Points.map f))

#check (AlgebraicGeometry.AlgebraicSpace.pointsIsQuotientMap_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    pointsIsQuotientMap f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isQuotientMapOnPoints τX τY f)

#check (AlgebraicGeometry.AlgebraicSpace.pointsIsQuotientMap.of :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
      IsPointsTopology X τX → IsPointsTopology Y τY → isQuotientMapOnPoints τX τY f),
    pointsIsQuotientMap f)

#check (AlgebraicGeometry.AlgebraicSpace.pointsIsQuotientMap.spec :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : pointsIsQuotientMap f) {τX : TopologicalSpace (Points X)}
    {τY : TopologicalSpace (Points Y)} (hX : IsPointsTopology X τX)
    (hY : IsPointsTopology Y τY),
    isQuotientMapOnPoints τX τY f)

#check (AlgebraicGeometry.AlgebraicSpace.pointsIsQuotientMap.pullback_snd :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : universally pointsIsQuotientMap f) (g : Z ⟶ Y) [HasPullback f g],
    pointsIsQuotientMap (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.universally_pointsIsQuotientMap_iff :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    universally pointsIsQuotientMap f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → pointsIsQuotientMap pZ)
