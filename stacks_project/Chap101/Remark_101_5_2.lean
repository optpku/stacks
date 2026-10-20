module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Group
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Remark 101.5.2: Let `f : X ⟶ Y` be a morphism of algebraic stacks. In the
1-category of morphisms `Z ⟶ X` representable by algebraic spaces, obtained as
the homotopy category of `SpacesOver X`, the relative inertia stack
`I_{X/Y}` is a group object. An object of `I_{X/Y}` is a pair `(x, α)` with
`x` an object of `X` and `α` an automorphism of `x` in its fibre category
satisfying `f(α) = id`. Multiplication
`I_{X/Y} ×_X I_{X/Y} ⟶ I_{X/Y}` is given on objects by
`((x, α), (x', α'), β) ↦ (x, α ∘ β⁻¹ ∘ α' ∘ β)`, and the unit
`X ⟶ I_{X/Y}` is `x ↦ (x, id_x)`. -/
@[stacks 050R] #check (AlgebraicGeometry.AlgebraicStack.RelativeInertia.instGrpObj :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    GrpObj (AlgebraicGeometry.AlgebraicStack.RelativeInertia.asHomotopy f))
