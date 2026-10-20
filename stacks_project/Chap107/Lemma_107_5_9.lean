module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeDimension
import StacksCheckRecall

/-!
# Base-change invariance of relative dimension

In a Cartesian square of locally Noetherian algebraic stacks whose vertical
arrows are locally of finite type, the relative dimension at a point is
unchanged by base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.5.9: Suppose given a Cartesian square of morphisms of locally
Noetherian algebraic stacks in which the vertical morphisms are locally of
finite type. If `t'` is a point of `|T'|`, with images `t = Points.map g' t'`,
`x' = Points.map f' t'`, and `x = Points.map f t` in `|T|`, `|X'|`, and `|X|`
respectively, then `relativeDimensionAt f' t' = relativeDimensionAt f t`. -/
@[stacks 0DRN] #check (AlgebraicGeometry.AlgebraicStack.relativeDimensionAt_eq_of_isBilimit :
    ∀ {S : Scheme.{u}}
    {T X T' X' : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack T'] [AlgebraicStack X']
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    [IsLocallyNoetherian T'] [IsLocallyNoetherian X']
    {f : T ⟶ X} {g : X' ⟶ X} {g' : T' ⟶ T} {f' : T' ⟶ X'}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (iso : g' ≫ f ≅ f' ≫ g) (h : (PseudoPullbackCone.mk f g T' g' f' iso).IsBilimit)
    (t' : Points T'),
    relativeDimensionAt f' t' = relativeDimensionAt f (Points.map g' t'))

end AlgebraicGeometry.AlgebraicStack
