module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Algebraic

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The source of an algebraic 1-morphism of stacks in groupoids over
`(Sch/S)_fppf` is an algebraic stack if its target is an algebraic stack. -/
@[stacks 05XY]
theorem of_algebraic {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [AlgebraicStack Y] (F : X ⟶ Y) [Groupoids.Hom.Algebraic F] :
    AlgebraicStack X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
