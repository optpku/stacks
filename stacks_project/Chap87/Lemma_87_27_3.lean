module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap87.Lemma_87_27_3_ClosedImmersion
public import stacks_project.Chap88.Definition_88_21_1_Formal

/-!
# Base change of closed immersions of formal algebraic spaces

A base change of a closed immersion of formal algebraic spaces is again a
closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.27.3: A base change of a closed immersion is a closed immersion. -/
@[stacks 0GHX]
theorem closedImmersion_of_isPullback {S : Scheme.{u}}
    {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Y'] [IsFormalAlgebraicSpace B]
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : ClosedImmersion g) :
    ClosedImmersion g' :=
  sorry

/-- The base-change projection `pullback.snd f g` of a closed immersion
`f : X ⟶ Y` of formal algebraic spaces is a closed immersion. -/
instance closedImmersion_pullback_snd {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [HasPullback f g] [IsFormalAlgebraicSpace (pullback f g)]
    [ClosedImmersion f] : ClosedImmersion (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
