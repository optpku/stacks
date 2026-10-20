module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Stack

/-!
# Algebraicity along morphisms representable by algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The source of a morphism of stacks in groupoids over `(Sch/S)_fppf`
representable by algebraic spaces is an algebraic stack if its target is an
algebraic stack. -/
@[stacks 05UM]
theorem of_relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p] [AlgebraicStack Y]
    (f : X ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f) :
    AlgebraicStack X :=
  sorry

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry

/-- The source of a morphism of categories fibred in groupoids over
`(Sch/S)_fppf` representable by algebraic spaces is an algebraic stack if its
target is an algebraic stack. -/
@[stacks 05UN]
theorem relativelyRepresentableByAlgebraicSpaces.source_isAlgebraicStack
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    AlgebraicStack X :=
  sorry

end AlgebraicGeometry
