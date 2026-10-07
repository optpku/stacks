module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# Open and universally open morphisms of algebraic spaces

A morphism of algebraic spaces is open when it induces an open map on
underlying point spaces, and universally open when every base change is open.
The canonical topology on `Points` is characterized rather than constructed, so
competing topologies remain explicit parameters.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The map on points induced by `f` is an open map with respect to the given
topologies on the source and target point spaces. -/
def isOpenMapOnPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @IsOpenMap (Points X) (Points Y) τX τY (Points.map f)

/-- Being an open map on points means open sets in the source point space have
open images in the target. -/
theorem isOpenMapOnPoints_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) :
    isOpenMapOnPoints τX τY f ↔
      ∀ (U : Set (Points X)),
        @IsOpen (Points X) τX U → @IsOpen (Points Y) τY (Points.map f '' U) :=
  sorry

/-- The morphism property of inducing an open map on canonical point spaces. -/
def pointsIsOpenMap {S : Scheme.{u}} : MorphismProperty (AlgebraicSpace S) :=
  fun {X Y} f ↦
    ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
      IsPointsTopology X τX → IsPointsTopology Y τY → isOpenMapOnPoints τX τY f

/-- A morphism induces an open map on points if it does so for every pair of
canonical topologies on the source and target. -/
theorem pointsIsOpenMap_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    pointsIsOpenMap f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isOpenMapOnPoints τX τY f :=
  sorry

/-- A morphism of algebraic spaces is open if the induced map on underlying
point spaces is an open map. -/
@[mk_iff]
class Open {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The map on points induced by `f` is open for every pair of canonical
  topologies. -/
  isOpenMap : pointsIsOpenMap f

namespace Open

/-- The identity morphism of an algebraic space is open. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Open (𝟙 X) := sorry

/-- An open morphism induces an open map on points for any pair of canonical
topologies. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [Open f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    isOpenMapOnPoints τX τY f :=
  sorry

/-- A morphism is open as soon as it induces an open map on canonical point
spaces. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : pointsIsOpenMap f) : Open f :=
  sorry

end Open

/-- A morphism of algebraic spaces is universally open if every base change
induces an open map on underlying point spaces. -/
@[mk_iff]
class UniversallyOpen {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every base change of `f` induces an open map on points. -/
  universally_isOpenMap : universally pointsIsOpenMap f

namespace UniversallyOpen

/-- The identity morphism of an algebraic space is universally open. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    UniversallyOpen (𝟙 X) :=
  sorry

/-- A universally open morphism has the `universally pointsIsOpenMap`
morphism property. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [UniversallyOpen f] : universally pointsIsOpenMap f :=
  sorry

/-- Every base change of a universally open morphism, expressed by an
`IsPullback` square, is an open morphism. -/
theorem isOpen_of_isPullback {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X}
    [UniversallyOpen f] (h : IsPullback pZ pX g f) : Open pZ :=
  sorry

/-- Universally open morphisms of algebraic spaces are stable under pullback
along an arbitrary morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : UniversallyOpen g) :
    UniversallyOpen g' :=
  sorry

/-- The base-change projection `pullback.snd f g : Z ×_Y X ⟶ Z` of a universally
open morphism `f : X ⟶ Y` is universally open. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : UniversallyOpen f) (g : Z ⟶ Y) [HasPullback f g] :
    UniversallyOpen (pullback.snd f g) :=
  sorry

end UniversallyOpen

/-- A universally open morphism of algebraic spaces is open. -/
instance instOpen_of_universallyOpen {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [UniversallyOpen f] : Open f :=
  sorry

/-- Typeclass form of base-change stability for a universally open morphism
along a morphism for which the pullback exists. -/
instance universallyOpen_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [UniversallyOpen f] [HasPullback f g] :
    UniversallyOpen (pullback.snd f g) :=
  sorry

/-- A morphism of algebraic spaces is universally open if and only if every
base change, expressed by an `IsPullback` square, is an open morphism. -/
theorem universallyOpen_iff_isOpen_of_isPullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    UniversallyOpen f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → Open pZ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
