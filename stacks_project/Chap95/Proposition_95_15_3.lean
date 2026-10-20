module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Quotient.Comparison

/-!
# Proposition 95.15.3

In Situation 95.15.1 there is a canonical equivalence `[X/G] ⟶ [[X/G]]` of
stacks in groupoids over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupAlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace
open AlgebraicGeometry.QuotientStack

universe u

/- Proposition 95.15.3: the canonical comparison from the fppf action-groupoid
quotient stack to the stack of torsors with an equivariant map is an equivalence. -/
@[stacks 04WM] #check
  (AlgebraicGeometry.QuotientStack.GroupAction.equivalent_isEquivalence :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      (G : GroupAlgebraicSpace B) (X : Action G),
      (GroupAction.equivalent G X).toBasedFunctor.IsEquivalence)

#check
  (AlgebraicGeometry.QuotientStack.GroupAction.equivalent :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      (G : GroupAlgebraicSpace B) (X : Action G),
      CartesianBasedFunctor (fppfQuotientStack (ofAction G X)).p
        (GroupAction.forget G X))
