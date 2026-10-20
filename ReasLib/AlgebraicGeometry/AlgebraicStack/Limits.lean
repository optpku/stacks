module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Equalizers in algebraic stacks

The total category of an algebraic stack over a scheme has equalizers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The total category of an algebraic stack over `S` has equalizers. -/
@[stacks 06WY]
instance hasEqualizers (X : GroupoidsOver S) [AlgebraicStack X] :
    HasEqualizers X.total := sorry

end AlgebraicGeometry.GroupoidsOver
