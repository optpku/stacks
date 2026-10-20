module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points

/-!
# Regularity of reduced locally Noetherian singleton algebraic stacks

A reduced, locally Noetherian algebraic stack whose space of points is a
singleton is regular.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A reduced, locally Noetherian algebraic stack `Z` such that
`|Z|` is a singleton is regular. -/
@[stacks 06MV]
instance isRegular_of_isReduced_isLocallyNoetherian_subsingleton
    {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z] [IsReduced Z]
    [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)] :
    IsRegular Z :=
  sorry

end AlgebraicGeometry.AlgebraicStack
