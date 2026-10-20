module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.EtaleSmoothLocal

@[expose] public section

open CategoryTheory

universe u

/- The étale-smooth-local-on-source-and-target lift of a morphism property is
defined by a mixed presentation with surjective source atlas. -/
#check (AlgebraicGeometry.AlgebraicStack.hasEtaleSmoothLocalAtSourceAndTarget :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (P : CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S))
    [AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y : AlgebraicGeometry.GroupoidsOver S}
    [AlgebraicGeometry.AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack Y],
    (X ⟶ Y) → Prop)
