module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiberDimension
import StacksCheckRecall

/-!
# Well-definedness of relative dimension for space-to-stack morphisms

Representing fibres give the same dimension, and for algebraic-space targets
this dimension agrees with the algebraic-space fibre dimension.
-/

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Remark 107.5.3 (1): the dimension at a representing fibre is independent
of the field-valued representative, fibre model, and lifted point. -/
@[stacks 0DRH] #check (AlgebraicGeometry.AlgebraicStack.fiberDimensionAt_independent :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : T.toGroupoids ⟶ X)
    [LocallyOfFiniteType f] (t : AlgebraicSpace.Points T)
    (w w' : RelativeDimensionChoice f t),
    w.dimension = w'.dimension)

/- Remark 107.5.3 (2): for an algebraic-space target, the dimension at a
representing fibre agrees with its algebraic-space relative dimension. -/
@[stacks 0DRH] #check (AlgebraicGeometry.AlgebraicStack.fiberDimensionAt_eq_of_algebraicSpace :
  ∀ {S : Scheme.{u}}
    {T Y : AlgebraicSpace S} (φ : T ⟶ Y) [AlgebraicSpace.LocallyOfFiniteType φ]
    (t : AlgebraicSpace.Points T)
    (w : RelativeDimensionChoice (AlgebraicSpace.toGroupoids.map φ) t),
    w.dimension = AlgebraicSpace.fiberDimensionAt φ t)

end AlgebraicGeometry.AlgebraicStack
