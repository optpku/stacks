/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism

/-!
# Open and universally open morphisms of algebraic spaces

A morphism of algebraic spaces is open when it induces an open map on
underlying point spaces with their canonical topologies, and universally open
when every base change is open.
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
    @IsOpenMap (Points X) (Points Y)
      (instTopologicalSpacePoints X) (instTopologicalSpacePoints Y) (Points.map f)

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
  /-- The map on points induced by `f` is open in the canonical topologies. -/
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

/-- Universally open morphisms of algebraic spaces are stable under base change. -/
instance universallyOpen_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@UniversallyOpen S : MorphismProperty (AlgebraicSpace S)) := sorry

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

/-- The base-change projection of a universally open morphism is universally open
whenever the pullback exists. -/
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

/-- For representable morphisms of algebraic spaces, universal openness tested on
represented scheme pullbacks agrees with universal openness on point spaces.
-/
theorem universallyOpen_presheaf_iff_universallyOpen
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversallyOpen : MorphismProperty Scheme.{u})).presheaf f ↔
      UniversallyOpen f :=
  sorry

/-- A representable morphism satisfying the scheme universal openness
property is universally open as a morphism of algebraic spaces. -/
theorem universallyOpen_of_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.UniversallyOpen : MorphismProperty Scheme.{u})).presheaf f) :
    UniversallyOpen f :=
  (universallyOpen_presheaf_iff_universallyOpen hf).mp h

/-- A representable universally open morphism satisfies the scheme universal
openness property. -/
theorem universallyOpen_presheaf_of_universallyOpen
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : UniversallyOpen f) :
    (over (@AlgebraicGeometry.UniversallyOpen : MorphismProperty Scheme.{u})).presheaf f :=
  (universallyOpen_presheaf_iff_universallyOpen hf).mpr h

/-- For representable morphisms, scheme universal openness is equivalent to
openness of every base change represented by an `IsPullback` square. -/
theorem universallyOpen_presheaf_iff_isOpen_of_isPullback
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversallyOpen : MorphismProperty Scheme.{u})).presheaf f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → Open pZ := by
  rw [universallyOpen_presheaf_iff_universallyOpen hf]
  exact universallyOpen_iff_isOpen_of_isPullback f

end AlgebraicGeometry.AlgebraicSpace
