module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Definition_101_37_1_FiniteType
public import stacks_project.Chap106.Lemma_106_11_1_DvrCommSq

/-!
# Reaching a point in the closure of the image by a Noetherian valuative square

A finite-type morphism of algebraic stacks to a locally Noetherian target
admits a discrete valuation ring valuative square through any point in the
closure of its image.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 106.11.1: if `f : X ⟶ Y` is a finite-type morphism of algebraic
stacks over a scheme `S` and `Y` is locally Noetherian, then every point `y`
of `|Y|` in the closure of the image of `|f|` is the image of the closed
point of `Spec(A)` in a 2-commutative valuative square `Spec(K) ⟶ X` over
`Spec(A) ⟶ Y`, where `A` is a discrete valuation ring and `K` is its field
of fractions. -/
@[stacks 0H2B]
theorem exists_dvrValuativeCommSq_of_mem_closure_range
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [FiniteType f] [IsLocallyNoetherian Y]
    {y : Points Y} {τ : TopologicalSpace (Points Y)}
    (hτ : IsPointsTopology Y τ)
    (hy : y ∈ @closure (Points Y) τ (Set.range (Points.map f))) :
    ∃ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R ∧ sq.closedPointImage = y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
