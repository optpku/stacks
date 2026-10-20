module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.Spaces
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- 81.11.0.1: the canonical functor Spaces/X ⟶ Spaces(Y → X, Z) sending
X' ⟶ X to U ×_X X' ← V ×_X X' → Y ×_X X', where Spaces(Y → X, Z) is the
category of commutative diagrams U' ← V' → Y' over U ← V → Y with both
squares cartesian. -/
@[stacks 0AF3] #check (AlgebraicGeometry.AlgebraicSpace.FormalGlueing.functor :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X),
    [IsClosedImmersion i] → Over X ⥤ AlgebraicGeometry.AlgebraicSpace.FormalGlueing.category f i)
