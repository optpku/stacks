/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_38_6_SchemeTheoreticImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.38.6: Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact morphism of algebraic
stacks. Let `𝒵 ⊂ 𝒴` be a scheme-theoretic image of `f`. Then `|𝒵|` is the
closure of the image of `|f|`. -/
@[stacks 0CML] #check
  (@AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage.closure_range_eq :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.QuasiCompact f]
      (toImage : X ⟶ Z) (ι : Z ⟶ Y)
      [AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage f toImage ι]
      {τY : TopologicalSpace (AlgebraicGeometry.AlgebraicStack.Points Y)},
      AlgebraicGeometry.AlgebraicStack.IsPointsTopology Y τY →
        @closure (AlgebraicGeometry.AlgebraicStack.Points Y) τY
            (Set.range (AlgebraicGeometry.AlgebraicStack.Points.map f)) =
          Set.range (AlgebraicGeometry.AlgebraicStack.Points.map ι))
