module

public import stacks_project.Chap100.Lemma_100_4_7_Topology

/-!
# Unique functorial topology on points of algebraic stacks

Let `S` be a scheme. The sets of points of algebraic stacks over `S` carry a unique
family of topologies such that every 1-morphism of algebraic stacks is continuous
on points, and every flat locally-of-finite-presentation 1-morphism from an
algebraic space is continuous and open on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.4.7 (1): the canonical topology on points of algebraic stacks over `S`
makes every 1-morphism of algebraic stacks continuous on points, and makes every
flat locally-of-finite-presentation 1-morphism from an algebraic space continuous
and open on points. -/
@[stacks 04XL]
theorem instTopologicalSpacePoints_spec (S : Scheme.{u}) :
    (∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      Continuous (Points.map f)) ∧
      ∀ {X : GroupoidsOver S} [AlgebraicStack X] {U : AlgebraicSpace S}
        (p : U.toGroupoids ⟶ X) [Groupoids.Hom.Flat p]
        [Groupoids.Hom.LocallyOfFinitePresentation p],
        Continuous (Points.mapSpace p) ∧ IsOpenMap (Points.mapSpace p) :=
  sorry

/-- Lemma 100.4.7 (2): a family of topologies on points of algebraic stacks over `S`
with functorial continuity and flat locally-of-finite-presentation openness from
algebraic spaces coincides with the canonical topology. -/
@[stacks 04XL]
theorem Points.unique {S : Scheme.{u}}
    (τ : ∀ (X : GroupoidsOver S) [AlgebraicStack X], TopologicalSpace (Points X))
    (h_continuous : ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y), Continuous[τ X, τ Y] (Points.map f))
    (h_fppf : ∀ {X : GroupoidsOver S} [AlgebraicStack X] {U : AlgebraicSpace S}
      (p : U.toGroupoids ⟶ X) [Groupoids.Hom.Flat p]
      [Groupoids.Hom.LocallyOfFinitePresentation p],
      Continuous[inferInstance, τ X] (Points.mapSpace p) ∧
        @IsOpenMap (AlgebraicSpace.Points U) (Points X) inferInstance (τ X)
          (Points.mapSpace p))
    (X : GroupoidsOver S) [AlgebraicStack X] :
    τ X = instTopologicalSpacePoints X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
