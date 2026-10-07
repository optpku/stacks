module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf

/-!
# Quotient sheaves associated to algebraic-space actions

This module identifies the quotient sheaf of an action with the quotient sheaf of its
associated action groupoid pre-relation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Action

/-- The quotient sheaf `U/G` associated to an action of a group algebraic space, as the
quotient sheaf of the corresponding action groupoid pre-relation. -/
abbrev quotientSheaf {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupAlgebraicSpace B} (X : Action G) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.quotientSheaf

/-- `Action.quotientSheaf` is the quotient sheaf of the action groupoid pre-relation. -/
theorem quotientSheaf_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupAlgebraicSpace B} (X : Action G) :
    quotientSheaf X =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.quotientSheaf := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Action
