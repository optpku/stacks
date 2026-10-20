module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.EtaleSmoothLocal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 101.34.2: let `P` be a property of morphisms of algebraic spaces
which is étale-smooth local on the source-and-target. A DM morphism
`f : X ⟶ Y` of algebraic stacks has property `P` when a mixed algebraic-space
presentation with smooth target leg, étale comparison, and surjective source
leg has `P` on its top arrow, equivalently when every such mixed square does. -/
@[stacks 0CIG] #check (AlgebraicGeometry.AlgebraicStack.hasEtaleSmoothLocalAtSourceAndTarget :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (P : CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S))
    [AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicGeometry.GroupoidsOver S}
    [AlgebraicGeometry.AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack Y],
    (X ⟶ Y) → Prop)
