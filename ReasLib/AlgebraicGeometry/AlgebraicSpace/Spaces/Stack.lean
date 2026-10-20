module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Groupoids
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids

/-!
# Stacks in groupoids of algebraic spaces

Finite-type algebraic spaces over schemes, with cartesian squares as morphisms,
and their finite-presentation, flat, proper full subcategory are stacks in
groupoids for the fppf topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- Finite-type algebraic spaces over schemes over `S`, with cartesian squares
as morphisms, form a stack in groupoids over `(Sch/S)_fppf`. -/
@[stacks 0D1G]
instance FtGroupoids.instIsStackInGroupoids (S : Scheme.{u}) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (pFtGroupoids S) := sorry

/-- The full subcategory of finite-presentation, flat, proper objects in
`FtGroupoids S` is a stack in groupoids over `(Sch/S)_fppf`. -/
@[stacks 0D1G]
instance FpFlatProperGroupoids.instIsStackInGroupoids (S : Scheme.{u}) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (pFpFlatProperGroupoids S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
