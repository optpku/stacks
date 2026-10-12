/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_38_1_SchemeTheoreticImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.38.1: Let `f : 𝒳 ⟶ 𝒴` be a morphism of algebraic stacks.
The scheme-theoretic image of `f` is the smallest closed substack `𝒵 ⊂ 𝒴`
through which `f` factors. -/
@[stacks 0CMI] #check AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage

/- A least closed-substack factorization of `f` is a scheme-theoretic image
factorization, recovering the smallest-closed-substack wording. -/
@[stacks 0CMI] #check
  (@AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage.of_isLeast_closedSubstack :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      (Z : AlgebraicStack.ClosedSubstack Y) (toImage : X ⟶ Z.Y),
      toImage ≫ Z.ι = f →
        (∀ Z' : AlgebraicStack.ClosedSubstack Y,
            (∃ toZ' : X ⟶ Z'.Y, toZ' ≫ Z'.ι = f) →
              ∃ k : Z.Y ⟶ Z'.Y, Nonempty (k ≫ Z'.ι ≅ Z.ι)) →
          AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage f toImage Z.ι)
