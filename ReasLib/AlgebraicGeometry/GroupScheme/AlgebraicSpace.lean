module

public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization.Tensor

/-! # Realization of group schemes as group algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupScheme

variable {S : Scheme.{u}}

/-- The group algebraic space over `S` associated to a group scheme `G` over `S`.
The underlying object is `ofOver` of `G.X`, and the structure maps are `ofOverMap`
of the scheme-level group operations. -/
def toGroupAlgebraicSpace (G : GroupScheme S) :
    GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk (𝟙 S))) where
  X := (AlgebraicSpace.SchemeRealization.ofOverSlice S).obj G.X
  grp :=
    { one := Over.homMk (AlgebraicSpace.SchemeRealization.ofOverMap η[G.X]) sorry
      mul := Over.homMk
        (AlgebraicSpace.SchemeRealization.sliceTensorComparison G.X G.X ≫ AlgebraicSpace.SchemeRealization.ofOverMap μ[G.X]) sorry
      inv := Over.homMk (AlgebraicSpace.SchemeRealization.ofOverMap ι[G.X]) sorry
      one_mul := sorry
      mul_one := sorry
      mul_assoc := sorry
      left_inv := sorry
      right_inv := sorry }

/-- The underlying slice object of `toGroupAlgebraicSpace G` is `ofOver` of `G.X`
over `S` as an algebraic space. -/
theorem toGroupAlgebraicSpace_X (G : GroupScheme S) :
    (toGroupAlgebraicSpace G).X = (AlgebraicSpace.SchemeRealization.ofOverSlice S).obj G.X := sorry

/-- The underlying algebraic space of `toGroupAlgebraicSpace G` is `ofOver G.X`. -/
theorem toGroupAlgebraicSpace_left (G : GroupScheme S) :
    (toGroupAlgebraicSpace G).X.left = AlgebraicSpace.ofOver G.X := sorry

end AlgebraicGeometry.GroupScheme
