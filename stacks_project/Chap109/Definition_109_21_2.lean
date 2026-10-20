module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Semistable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 109.21.2: a family of curves `f : X ⟶ S` is a semistable family
of curves if it is prestable and, for every point `s` of `S`, the fibre `X_s`
has genus at least `1` and has no rational tail. -/
@[stacks 0E6Z] #check (AlgebraicGeometry.AlgebraicSpace.Semistable :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)
