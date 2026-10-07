module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap87.Definition_87_25_1_Surjective
public import stacks_project.Chap88.Definition_88_18_1_Affine

/-!
# Base change of surjective morphisms of formal algebraic spaces

A base change of a surjective morphism of formal algebraic spaces is again
surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Surjective

/-- Lemma 87.25.3: A base change of a surjective morphism of formal algebraic
spaces is a surjective morphism. -/
@[stacks 0GHR]
theorem of_isPullback {S : Scheme.{u}}
    {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Y'] [IsFormalAlgebraicSpace B]
    [Reduction X] [Reduction Y] [Reduction Y'] [Reduction B]
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : Surjective g) : Surjective g' :=
  sorry

end Surjective

/-- The base-change projection `pullback.snd f g` of a surjective morphism
`f : X ⟶ Y` of formal algebraic spaces is surjective. -/
instance surjective_pullback_snd {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [Reduction X] [Reduction Y] [Reduction Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    [IsFormalAlgebraicSpace (pullback f g)] [Reduction (pullback f g)]
    [Surjective f] : Surjective (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
