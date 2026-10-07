module

public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Lemma_94_10_11

/-!
# Diagonal of a quotient stack

The diagonal of the quotient stack `[U/R]` associated to a groupoid in
algebraic spaces is representable by algebraic spaces. Smoothness of the
groupoid is not required.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 94.17.1: let `S` be a scheme contained in `Sch_fppf`. Let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over `S`. Then the
diagonal of `[U/R]` is representable by algebraic spaces. Formalized for a
groupoid `G` in algebraic spaces over an algebraic space `B` over `S`, with
`[U/R]` as `G.quotientStack` and the diagonal as
`FiberedCategoryOver.Groupoids.diagonal G.quotientStack`. -/
@[stacks 04WZ]
theorem relativelyRepresentableByAlgebraicSpaces_diagonal
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} G.quotientStack) :=
  sorry

/-- The isomorphism presheaves of the quotient stack `G.quotientStack` are
algebraic spaces. This is the Isom criterion used to deduce representability of
the diagonal via Lemma 94.10.11. -/
theorem isomorphismPresheaf_isAlgebraicSpace {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    isomorphismPresheaf.isAlgebraicSpace G.quotientStack :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
