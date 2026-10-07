module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Lemma_94_9_11
import StacksCheckRecall

/-!
# Sources of morphisms representable by algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 94.15.5 (1): let `S` be a scheme contained in `Sch_fppf`. Let
`f : X ⟶ Y` be a 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf`. Assume `f` is representable by algebraic spaces
(`hf : relativelyRepresentableByAlgebraicSpaces f`). If `Y` is a stack in
groupoids, then so is `X`. -/
@[stacks 05UN] #check relativelyRepresentableByAlgebraicSpaces.source_isStack

/-- Lemma 94.15.5 (2): let `S` be a scheme contained in `Sch_fppf`. Let
`f : X ⟶ Y` be a 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf`. Assume `f` is representable by algebraic spaces
(`hf : relativelyRepresentableByAlgebraicSpaces f`). If `Y` is an algebraic
stack (`[AlgebraicStack Y]`), then `X` is an algebraic stack over `S`. -/
@[stacks 05UN]
theorem relativelyRepresentableByAlgebraicSpaces.source_isAlgebraicStack
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    AlgebraicStack X :=
  sorry

end AlgebraicGeometry
