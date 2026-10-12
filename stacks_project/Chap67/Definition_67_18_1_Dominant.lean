/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# Dominant morphisms of algebraic spaces

A morphism of algebraic spaces is dominant when the induced map on associated
point spaces has dense image. The canonical topology on `Points` is
characterized rather than constructed, so competing topologies remain explicit
parameters.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The map on points induced by `f` has dense range with respect to the given
topology on the target point space. -/
def isDenseRangeOnPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τY : TopologicalSpace (Points Y)) (f : X ⟶ Y) : Prop :=
  @DenseRange (Points Y) τY (Points X) (Points.map f)

/-- Having dense range on points means the image of `Points.map f` is dense in the
target point space. -/
theorem isDenseRangeOnPoints_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τY : TopologicalSpace (Points Y)) (f : X ⟶ Y) :
    isDenseRangeOnPoints τY f ↔
      @Dense (Points Y) τY (Set.range (Points.map f)) :=
  sorry

/-- The morphism property of inducing a dense map on canonical point spaces. -/
def pointsIsDenseRange {S : Scheme.{u}} : MorphismProperty (AlgebraicSpace S) :=
  fun {X Y} (f : X ⟶ Y) ↦
    ∀ (τY : TopologicalSpace (Points Y)),
      IsPointsTopology Y τY → isDenseRangeOnPoints τY f

/-- A morphism induces a dense map on points if it does so for every canonical
topology on the target. -/
theorem pointsIsDenseRange_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    pointsIsDenseRange f ↔
      ∀ (τY : TopologicalSpace (Points Y)),
        IsPointsTopology Y τY → isDenseRangeOnPoints τY f :=
  sorry

/-- A morphism of algebraic spaces is dominant if the image of the induced map on
underlying point spaces is dense. -/
@[mk_iff]
class Dominant {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The map on points induced by `f` has dense range for every canonical
  topology on the target. -/
  denseRange : pointsIsDenseRange f

namespace Dominant

/-- The identity morphism of an algebraic space is dominant. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Dominant (𝟙 X) := sorry

/-- A surjective morphism of algebraic spaces is dominant. -/
instance of_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Surjective f] : Dominant f := sorry

/-- A dominant morphism has dense image on points for any canonical topology on
the target. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [Dominant f]
    {τY : TopologicalSpace (Points Y)} (hY : IsPointsTopology Y τY) :
    isDenseRangeOnPoints τY f :=
  sorry

/-- A morphism is dominant as soon as it induces a dense map on canonical point
spaces. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : pointsIsDenseRange f) : Dominant f :=
  sorry

end Dominant

end AlgebraicGeometry.AlgebraicSpace
