module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian

/-!
# Local Noetherianity of closed substacks

The restriction of a locally Noetherian algebraic stack to a closed object
property is locally Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack.Substack

/-- A closed substack of a locally Noetherian algebraic stack is locally Noetherian. -/
instance instIsLocallyNoetherian_closedCategory {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsLocallyNoetherian X]
    (P : ObjectProperty X.total) (hP : IsClosed X P) :
    IsLocallyNoetherian (closedCategory X P hP) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Substack
