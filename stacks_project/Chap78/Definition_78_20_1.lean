module

public import stacks_project.Chap78.Definition_78_20_1_Quotient
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

/- Definition 78.20.1 (1): the quotient stack p : [U/R] ⟶ (Sch/S)_fppf of a groupoid in
algebraic spaces (U, R, s, t, c) over B is the stackification of the category fibred in
groupoids [U/_p R] associated to the groupoid-valued functor of points. -/
@[stacks 044Q] #check
  (@GroupoidAlgebraicSpace.quotientStack :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S},
      GroupoidAlgebraicSpace B → StackOver.Groupoids (Scheme.fppfTopology.over S))

/- Definition 78.20.1 (2): the quotient stack p : [X/G] ⟶ (Sch/S)_fppf of an action of a
group algebraic space (G, m) over B on an algebraic space X over B is the quotient stack
associated to the action groupoid (X, G ×_B X, s, t, c) of Lemma 78.15.1. -/
@[stacks 044Q] #check
  (fun {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      (X : GroupAlgebraicSpace.Action G) ↦
    (GroupoidAlgebraicSpace.ofAction G X).quotientStack :
    {S : Scheme.{u}} → {B : AlgebraicSpace S} → (G : GroupAlgebraicSpace B) →
      GroupAlgebraicSpace.Action G →
        StackOver.Groupoids (Scheme.fppfTopology.over S))
