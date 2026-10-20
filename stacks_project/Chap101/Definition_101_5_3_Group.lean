module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Group

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.5.3 (1): relative automorphisms form a group
algebraic space over `Z` by pulling back composition on relative inertia. -/
#check (AlgebraicGeometry.AlgebraicStack.RelativeIsom.instGrpObj_asHomotopy :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X), GrpObj (AlgebraicGeometry.AlgebraicStack.RelativeIsom.asHomotopy f x))
