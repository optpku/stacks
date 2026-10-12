/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap100.Lemma_100_7_4_Points
public import stacks_project.Chap100.Lemma_100_14_1_QuasiCompact
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap103.«103_15_1_1_Smooth»

/-!
# Specializations along a smooth algebraic-space chart

A specialization of points of an algebraic stack lifts through a smooth morphism
from an algebraic space, provided the specialized point satisfies the
quasi-compact field-valued tests of Lemma 100.14.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.47.1: Let `X` be an algebraic stack. Let `f : U.toGroupoids ⟶ X` be
a `Smooth` morphism where `U` is an algebraic space. Let `x' ⤳ x` be a
`Specializes` relation of points of `Points X` in an `IsPointsTopology`. Let
`u` be a point of `AlgebraicSpace.Points U` with `Points.mapSpace f u = x`. If
`(X, x')` satisfy `existsQuasiCompactFieldValuedPoint`, then there exists a
specialization `u' ⤳ u` in `AlgebraicSpace.Points U` with
`Points.mapSpace f u' = x'`. -/
@[stacks 0GVZ]
theorem exists_specializes_of_smooth {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : U.toGroupoids ⟶ X) [Smooth f]
    {x x' : Points X} {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (hspec : @Specializes (Points X) τ x' x)
    (h_quasiCompact : existsQuasiCompactFieldValuedPoint X x')
    {u : AlgebraicSpace.Points U} (hu : Points.mapSpace f u = x) :
    ∃ u' : AlgebraicSpace.Points U,
      Specializes u' u ∧ Points.mapSpace f u' = x' :=
  sorry

/-- The same specialization-lifting along a smooth algebraic-space chart, with
the equivalent universal quasi-compact field-valued test
`forallFieldValuedPointQuasiCompact` in place of
`existsQuasiCompactFieldValuedPoint`. -/
theorem exists_specializes_of_smooth_of_forallFieldValuedPointQuasiCompact
    {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] (f : U.toGroupoids ⟶ X) [Smooth f] {x x' : Points X}
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (hspec : @Specializes (Points X) τ x' x)
    (h_quasiCompact : forallFieldValuedPointQuasiCompact X x')
    {u : AlgebraicSpace.Points U} (hu : Points.mapSpace f u = x) :
    ∃ u' : AlgebraicSpace.Points U,
      Specializes u' u ∧ Points.mapSpace f u' = x' :=
  sorry

end AlgebraicGeometry.AlgebraicStack
