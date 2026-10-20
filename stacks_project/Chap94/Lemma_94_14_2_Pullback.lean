module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct

/-!
# 2-fibre products of algebraic stacks over a stack with representable diagonal

If `Z` is a stack in groupoids over `(Sch/S)_fppf` whose diagonal is representable
by algebraic spaces, and `X`, `Y` are algebraic stacks over `S`, then the
2-fibre product of 1-morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` is an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.twoFibreProduct :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Z.p]
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Z)),
    AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g))
