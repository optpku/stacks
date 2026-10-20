module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
universe u

/- Situation 99.15.1: Curves has algebraic-space total spaces, scheme bases,
flat proper finitely presented structure morphisms of relative dimension at most one,
and cartesian morphisms. -/
@[stacks 0D4Z] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.Obj : Scheme.{u} → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.p :
  ∀ S : Scheme.{u}, AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.Obj S ⥤ Over S)
