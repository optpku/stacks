module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Group

/-! Relative inertia, with its explicit multiplication, identity section, and inversion. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.RelativeInertia.instGrpObj :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    GrpObj (AlgebraicGeometry.AlgebraicStack.RelativeInertia.asHomotopy f))
