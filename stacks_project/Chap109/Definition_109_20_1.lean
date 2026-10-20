module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Prestable
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 109.20.1: a family of curves `f : X ⟶ S` is prestable if it is
at-worst-nodal of relative dimension 1 and `𝒪_S ⟶ f_* 𝒪_X` is an isomorphism
after any base change. -/
@[stacks 0E6T] #check (AlgebraicGeometry.AlgebraicSpace.Prestable :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)
