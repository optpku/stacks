/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism
public import stacks_project.Chap70.Lemma_70_21_1_DvrCommSq

/-!
# Reaching a point in the closure of the image by a Noetherian valuative square

A finite-type morphism of algebraic spaces to a locally Noetherian target admits a DVR-or-field
valuative square through any point in the closure of its image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 70.21.1: if `f : X ⟶ Y` is a finite-type morphism of algebraic spaces over a scheme
`S` and `Y` is locally Noetherian, then every point `y` of `|Y|` in the closure of the image of
`|f|` is the image of the closed point of `Spec(A)` in a commutative valuative square
`Spec(K) ⟶ X` over `Spec(A) ⟶ Y`, where `A` is a discrete valuation ring or a field and
`K` is its field of fractions. The source point of `Spec(K) ⟶ X` may be taken of étale-local
codimension `0`, with `K` the residue field of a point of a scheme étale over `X`. -/
@[stacks 0CMC]
theorem exists_dvrOrFieldValuativeCommSqAt_of_mem_closure_range
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [IsLocallyNoetherian Y]
    {y : Points Y} {τ : TopologicalSpace (Points Y)}
    (hτ : IsPointsTopology Y τ)
    (hy : y ∈ @closure (Points Y) τ (Set.range (Points.map f))) :
    ∃ sq : DvrOrFieldValuativeCommSqAt f, sq.closedPointImage = y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
