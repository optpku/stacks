/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Defs.Induced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison

/-!
# Universal homeomorphisms of algebraic spaces

A morphism of algebraic spaces is a universal homeomorphism when every base change
induces a homeomorphism on underlying point spaces. The canonical topology on
`Points` is characterized, rather than constructed, so competing topologies remain
explicit parameters.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A topology on the points of an algebraic space is the canonical one when every
representable étale locally-surjective atlas is a quotient map onto those points. -/
def IsPointsTopology {S : Scheme.{u}} (X : AlgebraicSpace S)
    (τ : TopologicalSpace (Points X)) : Prop :=
  ∀ (U : Over S) (p : ofOver U ⟶ X),
    (MorphismProperty.over (@Etale)).presheaf p →
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p →
        @Topology.IsQuotientMap U.left (Points X)
          (inferInstance : TopologicalSpace U.left) τ
          (fun u ↦ Points.map p (ofOver.pointsEquiv U u))

/-- The topology coinduced along `ofOver.pointsEquiv` is the canonical topology on
points of a representable algebraic space. -/
theorem isPointsTopology_ofOver {S : Scheme.{u}} (U : Over S) :
    IsPointsTopology (ofOver U)
      (TopologicalSpace.coinduced (fun u ↦ ofOver.pointsEquiv U u)
        (inferInstance : TopologicalSpace U.left)) := sorry

/-- A canonical topology on points makes every representable étale locally-surjective
atlas a quotient map. -/
theorem isPointsTopology_isQuotientMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    {U : Over S} {p : ofOver U ⟶ X}
    (hp_etale : (MorphismProperty.over (@Etale)).presheaf p)
    (hp_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p) :
    @Topology.IsQuotientMap U.left (Points X)
      (inferInstance : TopologicalSpace U.left) τ
      (fun u ↦ Points.map p (ofOver.pointsEquiv U u)) := sorry

/-- The map on points induced by `f` is a homeomorphism with respect to the given
topologies on the source and target point spaces. -/
def isHomeomorphOnPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @IsHomeomorph (Points X) (Points Y) τX τY (Points.map f)

/-- Being a homeomorphism on points means the induced map is continuous, open, and
bijective for the given topologies. -/
theorem isHomeomorphOnPoints_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) :
    isHomeomorphOnPoints τX τY f ↔
      @Continuous (Points X) (Points Y) τX τY (Points.map f) ∧
        @IsOpenMap (Points X) (Points Y) τX τY (Points.map f) ∧
          Function.Bijective (Points.map f) := sorry

/-- The morphism property of inducing a homeomorphism on canonical point spaces. -/
def pointsIsHomeomorph {S : Scheme.{u}} : MorphismProperty (AlgebraicSpace S) :=
  fun {X Y} f ↦
    ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
      IsPointsTopology X τX → IsPointsTopology Y τY → isHomeomorphOnPoints τX τY f

/-- A morphism induces a homeomorphism on points if it does so for every pair of
canonical topologies on the source and target. -/
theorem pointsIsHomeomorph_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    pointsIsHomeomorph f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isHomeomorphOnPoints τX τY f := sorry

/-- A morphism of algebraic spaces is a universal homeomorphism if every base change
induces a homeomorphism on underlying point spaces. -/
@[mk_iff]
class UniversalHomeomorphism {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every base change of `f` induces a homeomorphism on points. -/
  universally_isHomeomorph : universally pointsIsHomeomorph f

namespace UniversalHomeomorphism

/-- The identity morphism of an algebraic space is a universal homeomorphism. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    UniversalHomeomorphism (𝟙 X) := sorry

/-- Universal homeomorphisms are stable under pullback along an arbitrary morphism,
expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : UniversalHomeomorphism g) :
    UniversalHomeomorphism g' := sorry

/-- The base-change projection `pullback.snd f g : Z ×_Y X ⟶ Z` of a universal
homeomorphism `f : X ⟶ Y` is a universal homeomorphism. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : UniversalHomeomorphism f) (g : Z ⟶ Y) [HasPullback f g] :
    UniversalHomeomorphism (pullback.snd f g) := sorry

end UniversalHomeomorphism

/-- Universal homeomorphisms of algebraic spaces are stable under arbitrary base change. -/
instance universalHomeomorphism_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@UniversalHomeomorphism S : MorphismProperty (AlgebraicSpace S)) where
  of_isPullback := by
    intros
    apply UniversalHomeomorphism.of_isPullback <;> assumption

/-- Typeclass form of base-change stability for a universal homeomorphism along a
morphism for which the pullback exists. -/
instance universalHomeomorphism_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [UniversalHomeomorphism f] [HasPullback f g] :
    UniversalHomeomorphism (pullback.snd f g) := sorry

/-- Universal homeomorphisms of algebraic spaces are stable under composition. -/
instance universalHomeomorphism_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@UniversalHomeomorphism S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of universal homeomorphisms of algebraic spaces is a
universal homeomorphism. -/
instance universalHomeomorphism_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversalHomeomorphism f] [UniversalHomeomorphism g] :
    UniversalHomeomorphism (f ≫ g) :=
  MorphismProperty.comp_mem
    (@UniversalHomeomorphism S : MorphismProperty (AlgebraicSpace S))
    f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
