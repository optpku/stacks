module

public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_9_10_Substack

/-!
# Zariski-locality of representability by algebraic spaces

An algebraic stack that is a union of open substacks each representable by
an algebraic space is itself representable by an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.9.16: Let `X` be an algebraic stack. Let `U i`, `i : I`, be a
set of open substacks of `X`. Assume the images of
`Points.map (U i).ι : |(U i).Y| → |X|` cover `|X|`, and each `(U i).Y` is
representable by an algebraic space. Then `X` is representable by an
algebraic space. -/
@[stacks 05WE]
theorem isRepresentableByAlgebraicSpace_of_iUnion_openSubstack
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {I : Type v}
    (U : I → OpenSubstack X)
    (h_cover : ∀ x : Points X, ∃ i, x ∈ Set.range (Points.map (U i).ι))
    (h_space : ∀ i, IsRepresentableByAlgebraicSpace (U i).Y) :
    IsRepresentableByAlgebraicSpace X := sorry

end AlgebraicGeometry.AlgebraicStack
