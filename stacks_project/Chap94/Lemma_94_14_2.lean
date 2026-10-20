module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 94.14.2: let `S` be a scheme contained in `Sch_fppf`. Let `Z` be a
stack in groupoids over `(Sch/S)_fppf` whose diagonal is representable by
algebraic spaces. Let `X`, `Y` be algebraic stacks over `S`. Let `f : X ⟶ Z`,
`g : Y ⟶ Z` be 1-morphisms of stacks in groupoids. Then the 2-fibre product
`X ×_{f, Z, g} Y` is an algebraic stack. -/
@[stacks 04TF]
#check (AlgebraicGeometry.AlgebraicStack.twoFibreProduct :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Z.p]
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Z)),
    AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g))
