module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleAt
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 67.39.1: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is étale at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x` has
étale restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 04RH] #check (AlgebraicGeometry.AlgebraicSpace.EtaleAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → AlgebraicGeometry.AlgebraicSpace.Points X → Prop)
