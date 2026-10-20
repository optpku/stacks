module

public import ReasLib.AlgebraicGeometry.GroupScheme.AlgebraicSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Over

/-! # Group schemes as group algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.GroupScheme.toGroupAlgebraicSpace :
  ∀ {S : Scheme.{u}} (G : GroupScheme S),
    GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk (𝟙 S))))

#check (AlgebraicGeometry.GroupScheme.toGroupAlgebraicSpace_X :
  ∀ {S : Scheme.{u}} (G : GroupScheme S),
    (GroupScheme.toGroupAlgebraicSpace G).X =
      (AlgebraicSpace.SchemeRealization.ofOverSlice S).obj G.X)
