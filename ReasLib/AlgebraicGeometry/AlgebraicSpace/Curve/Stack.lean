module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids

/-!
# The stack of families of curves

Families of curves over schemes, with cartesian squares as morphisms, form a
stack in groupoids for the fppf topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- Families of curves over schemes over `S`, with cartesian squares as
morphisms, form a stack in groupoids over `(Sch/S)_fppf`. -/
@[stacks 0D52]
instance instIsStackInGroupoids (S : Scheme.{u}) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p S) := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
