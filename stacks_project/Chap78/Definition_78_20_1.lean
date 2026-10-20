module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Action
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

/- Definition 78.20.1 (1): the quotient stack p : [U/R] ⟶ (Sch/S)_fppf of a groupoid in
algebraic spaces (U, R, s, t, c) over B is the stackification of the category fibred in
groupoids [U/_p R] associated to the groupoid-valued functor of points. -/
@[stacks 044Q] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.fppfQuotientStack :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S},
      GroupoidAlgebraicSpace B → StackOver.Groupoids (Scheme.fppfTopology.over S))

/- Definition 78.20.1 (2): the quotient stack p : [X/G] ⟶ (Sch/S)_fppf of an action of a
group algebraic space (G, m) over B on an algebraic space X over B is the quotient stack
associated to the action groupoid (X, G ×_B X, s, t, c) of Lemma 78.15.1. -/
@[stacks 044Q] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.Action.fppfQuotientStack :
    {S : Scheme.{u}} → {B : AlgebraicSpace S} → (G : GroupAlgebraicSpace B) →
      GroupAlgebraicSpace.Action G →
        StackOver.Groupoids (Scheme.fppfTopology.over S))
