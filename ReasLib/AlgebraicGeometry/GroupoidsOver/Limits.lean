module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Diagonal

/-!
# Limits in categories fibred in groupoids over schemes

The total category of a groupoid fibration over schemes has pullbacks. It also
has equalizers when its isomorphism presheaves are algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The total category of a category fibred in groupoids over schemes over `S`
has pullbacks. -/
@[stacks 06WY]
instance hasPullbacks (X : GroupoidsOver S) : HasPullbacks X.total := sorry

/-- The total category of a category fibred in groupoids over schemes over `S`
has equalizers if its isomorphism presheaves are algebraic spaces. -/
@[stacks 06WY]
theorem hasEqualizers_of_isomorphismPresheaf (X : GroupoidsOver S)
    (h : isomorphismPresheaf.isAlgebraicSpace X) :
    HasEqualizers X.total := sorry

end AlgebraicGeometry.GroupoidsOver
