module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action

@[expose] public section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Action

/-- The fppf quotient stack `[X/G]` of an action of a group algebraic space over `B` is
the quotient stack of its associated action groupoid. -/
noncomputable def fppfQuotientStack {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    CategoryTheory.StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  AlgebraicGeometry.GroupoidAlgebraicSpace.fppfQuotientStack
    (AlgebraicGeometry.GroupoidAlgebraicSpace.ofAction G X)

end AlgebraicGeometry.GroupAlgebraicSpace.Action
