module

public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_9_10_Substack

/-!
# Zariski-locality of representability by schemes

An algebraic stack that is a union of open substacks each equivalent to a
scheme is itself a scheme, i.e. representable as a category fibred in
groupoids over `Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.9.17: Let `X` be an algebraic stack. Let `U i`, `i : I`, be a
set of open substacks of `X`. Assume the images of
`Points.map (U i).ι : |(U i).Y| → |X|` cover `|X|`, and each `(U i).Y` is a
scheme in the sense of `FiberedCategoryOver.Groupoids.IsRepresentable`. Then
`X` is a scheme. -/
@[stacks 05WF]
theorem isRepresentable_of_iUnion_openSubstack
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {I : Type v}
    (U : I → OpenSubstack X)
    (h_cover : ∀ x : Points X, ∃ i, x ∈ Set.range (Points.map (U i).ι))
    (h_scheme : ∀ i, FiberedCategoryOver.Groupoids.IsRepresentable (U i).Y) :
    FiberedCategoryOver.Groupoids.IsRepresentable X := sorry

end AlgebraicGeometry.AlgebraicStack
