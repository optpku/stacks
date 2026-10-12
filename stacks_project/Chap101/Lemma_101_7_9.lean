/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap106.Lemma_106_11_1_DvrCommSq

/-!
# Reaching a point in the closure of the image by a quasi-compact valuative square

A quasi-compact morphism of algebraic stacks admits a valuative square through
any point in the closure of its image.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.7.9: if `f : X ⟶ Y` is a quasi-compact morphism of algebraic
stacks over a scheme `S`, then every point `y` of `|Y|` in the closure of the
image of `|f|` is the image of the closed point of `Spec(A)` in a 2-commutative
valuative square `Spec(K) ⟶ X` over `Spec(A) ⟶ Y`, where `A` is a valuation
ring and `K` is its field of fractions. -/
@[stacks 0CL2]
theorem exists_valuativeCommSq_of_mem_closure_range
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiCompact f]
    {y : Points Y} {τ : TopologicalSpace (Points Y)}
    (hτ : IsPointsTopology Y τ)
    (hy : y ∈ @closure (Points Y) τ (Set.range (Points.map f))) :
    ∃ sq : ValuativeCommSq f, sq.closedPointImage = y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
