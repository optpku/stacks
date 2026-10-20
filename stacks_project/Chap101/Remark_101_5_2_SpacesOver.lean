module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SpacesOver.Cartesian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Group

/-! The cartesian category of algebraic spaces over an algebraic stack and its
relative-inertia object. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.SpacesOver.instCartesianMonoidalCategory_homotopy :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    CartesianMonoidalCategory (Bicategory.HomotopyCategory (SpacesOver X)))

#check (AlgebraicGeometry.AlgebraicStack.RelativeInertia.asSpacesOver :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y), SpacesOver X)
