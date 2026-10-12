/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_6_Topology

/-!
# Unique functorial topology on points of algebraic spaces

Let `S` be a scheme. The sets of points of algebraic spaces over `S` carry a unique
family of topologies such that schemes recover their usual topology along the
identification of Lemma 66.4.2, every morphism of algebraic spaces is continuous on
points, and every étale morphism from a scheme is continuous and open on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.4.6 (1): the canonical topology on points of algebraic spaces over `S`
recovers the usual scheme topology along `ofOver.pointsEquiv`, makes every morphism of
algebraic spaces continuous on points, and makes every étale morphism from a scheme
continuous and open on points. -/
@[stacks 03BX]
theorem instTopologicalSpacePoints_spec (S : Scheme.{u}) :
    (∀ X : Over S, IsHomeomorph (ofOver.pointsEquiv X)) ∧
      (∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y), Continuous (Points.map f)) ∧
        ∀ {X : AlgebraicSpace S} {U : Over S} (p : ofOver U ⟶ X),
          (MorphismProperty.over (@Etale)).presheaf p →
            Continuous (Points.mapOfOver p) ∧ IsOpenMap (Points.mapOfOver p) :=
  sorry

/-- Lemma 66.4.6 (2): a family of topologies on points of algebraic spaces over `S` with
the usual topology on schemes, functorial continuity, and étale openness from schemes
coincides with the canonical topology. -/
@[stacks 03BX]
theorem Points.unique {S : Scheme.{u}}
    (τ : ∀ X : AlgebraicSpace S, TopologicalSpace (Points X))
    (h_scheme : ∀ X : Over S,
      τ (ofOver X) = TopologicalSpace.coinduced (ofOver.pointsEquiv X) inferInstance)
    (h_continuous : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      Continuous[τ X, τ Y] (Points.map f))
    (h_etale : ∀ {X : AlgebraicSpace S} {U : Over S} (p : ofOver U ⟶ X),
      (MorphismProperty.over (@Etale)).presheaf p →
        Continuous[inferInstance, τ X] (Points.mapOfOver p) ∧
          @IsOpenMap U.left (Points X) inferInstance (τ X) (Points.mapOfOver p))
    (X : AlgebraicSpace S) :
    τ X = instTopologicalSpacePoints X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
