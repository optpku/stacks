module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormallySmooth
import StacksCheckRecall

/-!
# Reformulation of formal smoothness

A morphism of algebraic stacks is formally smooth if and only if every
first-order affine thickening diagram has a nonempty category of dotted arrows.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 106.8.2. A morphism of algebraic stacks is formally smooth if and only if
every first-order affine thickening diagram, with its specified comparison,
has a nonempty category of dotted arrows. -/
@[stacks 0DNY] #check
  (AlgebraicGeometry.AlgebraicStack.FormallySmooth.iff_nonempty_dottedArrow :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    FormallySmooth f ↔
      ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
        (i : T ⟶ T') [IsFirstOrderThickening i.left]
        (x : GroupoidsOver.slice T ⟶ X) (y : GroupoidsOver.slice T' ⟶ Y)
        (γ : overMap i ≫ y ≅ x ≫ f),
        Nonempty (DottedArrow
          (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ :
            Bicategory.PseudoPullbackCone y f)))

end AlgebraicGeometry.AlgebraicStack
