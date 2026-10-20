module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
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

/- Lemma 100.4.7 (1): the canonical topology makes every morphism of algebraic
stacks continuous and every flat locally-of-finite-presentation morphism from
an algebraic space continuous and open on points. -/
@[stacks 04XL] #check (AlgebraicGeometry.AlgebraicStack.instTopologicalSpacePoints_spec :
    ∀ (S : Scheme.{u}),
    (∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      Continuous (Points.map f)) ∧
      ∀ {X : GroupoidsOver S} [AlgebraicStack X] {U : AlgebraicSpace S}
        (p : U.toGroupoids ⟶ X) [Groupoids.Hom.Flat p]
        [Groupoids.Hom.LocallyOfFinitePresentation p],
        Continuous (Points.mapSpace p) ∧ IsOpenMap (Points.mapSpace p))

/- Lemma 100.4.7 (2): these continuity and openness properties uniquely determine
the family of topologies on algebraic-stack points. -/
@[stacks 04XL] #check (AlgebraicGeometry.AlgebraicStack.Points.unique :
    ∀ {S : Scheme.{u}}
    (τ : ∀ (X : GroupoidsOver S) [AlgebraicStack X], TopologicalSpace (Points X))
    (h_continuous : ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y), Continuous[τ X, τ Y] (Points.map f))
    (h_fppf : ∀ {X : GroupoidsOver S} [AlgebraicStack X] {U : AlgebraicSpace S}
      (p : U.toGroupoids ⟶ X) [Groupoids.Hom.Flat p]
      [Groupoids.Hom.LocallyOfFinitePresentation p],
      Continuous[inferInstance, τ X] (Points.mapSpace p) ∧
        @IsOpenMap (AlgebraicSpace.Points U) (Points X) inferInstance (τ X)
          (Points.mapSpace p))
    (X : GroupoidsOver S) [AlgebraicStack X],
    τ X = instTopologicalSpacePoints X)

end AlgebraicGeometry.AlgebraicStack
