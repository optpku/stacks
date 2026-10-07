module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable

/-!
# Cancellation of representability by algebraic spaces along postcomposition

If the relative diagonal of `b : G ⟶ H` and the composite `a ≫ b` are
representable by algebraic spaces, then so is `a`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.3.10: let `S` be a scheme. For maps `a : F ⟶ G` and `b : G ⟶ H` of
presheaves on `(Sch/S)_fppf`, if the relative diagonal
`pullback.diagonal b : G ⟶ pullback b b` (Stacks `Δ : G ⟶ G ×_H G`) and the
composite `a ≫ b` (Stacks `b ∘ a`) are representable by algebraic spaces, then
so is `a`. -/
@[stacks 0AMN]
theorem representableByAlgebraicSpaces.of_comp {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    [HasPullback b b] (hΔ : representableByAlgebraicSpaces (pullback.diagonal b))
    (hab : representableByAlgebraicSpaces (a ≫ b)) :
    representableByAlgebraicSpaces a :=
  sorry

/-- Representability by algebraic spaces cancels against postcomposition when the
relative diagonal of the second map is representable by algebraic spaces. -/
instance representableByAlgebraicSpaces.hasOfPostcompProperty_diagonal
    {S : Scheme.{u}} [HasPullbacks ((Over S)ᵒᵖ ⥤ Type u)] :
    (@representableByAlgebraicSpaces S).HasOfPostcompProperty
      (@representableByAlgebraicSpaces S).diagonal :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
