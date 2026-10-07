module

public import stacks_project.Chap101.Definition_101_28_1_Gerbe
public import stacks_project.Chap101.Lemma_101_25_5_Surjective
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap94.Lemma_94_14_3_Pullback

/-!
# When a morphism of algebraic stacks is a gerbe

A morphism of algebraic stacks makes the source a gerbe over the target if and
only if both the morphism and its relative 2-diagonal are surjective, flat, and
locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Proposition 101.28.11: let `f : X ⟶ Y` be a morphism of algebraic stacks.
Then `X` is a gerbe over `Y` if and only if `f` and the relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` are surjective, flat, and locally of finite
presentation. -/
@[stacks 0CPS]
theorem gerbe_iff_surjective_flat_locallyOfFinitePresentation_diagonal
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Gerbe f ↔
      Surjective f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        Surjective (Hom.diagonal.{u + 1, u, u + 1} f) ∧
          Flat (Hom.diagonal.{u + 1, u, u + 1} f) ∧
            LocallyOfFinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- A morphism of algebraic stacks that is surjective, flat, and locally of
finite presentation, and whose relative 2-diagonal is likewise surjective,
flat, and locally of finite presentation, is a gerbe over its target. -/
instance instGerbe_of_surjective_flat_locallyOfFinitePresentation_diagonal
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    [Surjective (Hom.diagonal.{u + 1, u, u + 1} f)]
    [Flat (Hom.diagonal.{u + 1, u, u + 1} f)]
    [LocallyOfFinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f)] :
    Gerbe f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
