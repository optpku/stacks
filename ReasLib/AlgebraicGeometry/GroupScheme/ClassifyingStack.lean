module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OfScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small

/-!
# Classifying stacks of group schemes
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme AlgebraicGeometry.GroupoidScheme

noncomputable section

universe u

namespace AlgebraicGeometry.HomStack

/-- The classifying stack `[S / A]` of a group scheme `A` over `S`, as the
quotient stack of the trivial action of `A` on `S`. This is the stack of fppf
`A`-torsors, pinned to `GroupoidsOver S`. -/
def classifyingTorsors {S : Scheme.{u}} (A : GroupScheme S) : GroupoidsOver S :=
  GroupoidAlgebraicSpace.SmallQuotient.quotientStack
      (GroupoidAlgebraicSpace.ofScheme (ofAction A (trivialAction A)))

/-- `classifyingTorsors A` is the quotient stack of the trivial action of `A`. -/
theorem classifyingTorsors_eq {S : Scheme.{u}} (A : GroupScheme S) :
    classifyingTorsors A =
      GroupoidAlgebraicSpace.SmallQuotient.quotientStack
      (GroupoidAlgebraicSpace.ofScheme (ofAction A (trivialAction A))) := rfl

end AlgebraicGeometry.HomStack
