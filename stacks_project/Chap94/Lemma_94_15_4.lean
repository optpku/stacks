module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Algebraicity along morphisms representable by algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 94.15.4: let `S` be a scheme contained in `Sch_fppf`. Let
`f : X ⟶ Y` be a 1-morphism of stacks in groupoids over `(Sch/S)_fppf`,
i.e. `[IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]` and
`[AlgebraicStack Y]`. If `f` is representable by algebraic spaces
(`hf : relativelyRepresentableByAlgebraicSpaces f`), then `X` is an
algebraic stack over `S`. -/
@[stacks 05UM]
theorem of_relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p] [AlgebraicStack Y]
    (f : X ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f) :
    AlgebraicStack X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
