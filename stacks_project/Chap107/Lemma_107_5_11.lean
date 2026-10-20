module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeDimension.Semicontinuity
import StacksCheckRecall

/-!
# Semicontinuity of relative dimension

For a locally of finite type morphism of locally Noetherian algebraic stacks,
relative dimension is upper semi-continuous on the space of points, and locally
constant when the morphism is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.5.11 (1): if `f : T ⟶ X` is a locally of finite type morphism of
locally Noetherian algebraic stacks, then `relativeDimensionAt f` is upper
semi-continuous on `Points T` in the canonical topology. -/
@[stacks 0DRQ] #check
  (AlgebraicGeometry.AlgebraicStack.upperSemicontinuous_relativeDimensionAt :
    ∀ {S : Scheme.{u}} {T X : GroupoidsOver S} [AlgebraicStack T] [AlgebraicStack X]
      [IsLocallyNoetherian T] [IsLocallyNoetherian X] (f : T ⟶ X)
      [LocallyOfFiniteType f], UpperSemicontinuous (relativeDimensionAt f))

/- Lemma 107.5.11 (2): if in addition `f` is smooth, then
`relativeDimensionAt f` is locally constant on `Points T` in the canonical
topology. -/
@[stacks 0DRQ] #check
  (AlgebraicGeometry.AlgebraicStack.isLocallyConstant_relativeDimensionAt :
    ∀ {S : Scheme.{u}} {T X : GroupoidsOver S} [AlgebraicStack T] [AlgebraicStack X]
      [IsLocallyNoetherian T] [IsLocallyNoetherian X] (f : T ⟶ X)
      [LocallyOfFiniteType f] [Smooth f], IsLocallyConstant (relativeDimensionAt f))

end AlgebraicGeometry.AlgebraicStack
