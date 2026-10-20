module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
import StacksCheckRecall

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

/- Lemma 66.4.6: there is a unique compatible family of topologies on algebraic-space points. -/
@[stacks 03BX] #check
  (AlgebraicGeometry.AlgebraicSpace.Points.existsUnique_topology :
    ∀ S : Scheme.{u},
      ∃! τ : ∀ X : AlgebraicSpace S, TopologicalSpace (Points X),
        (∀ U : Over S,
          τ (ofOver U) = TopologicalSpace.coinduced (ofOver.pointsEquiv U) inferInstance) ∧
        (∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
          Continuous[τ X, τ Y] (Points.map f)) ∧
        (∀ {X : AlgebraicSpace S} {U : Over S} (p : ofOver U ⟶ X),
          (MorphismProperty.over (@Etale)).presheaf p →
            Continuous[inferInstance, τ X] (Points.mapOfOver p) ∧
              @IsOpenMap U.left (Points X) inferInstance (τ X) (Points.mapOfOver p)))

end AlgebraicGeometry.AlgebraicSpace
