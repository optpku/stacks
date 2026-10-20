module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 67.40.1: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is proper if it is separated, finite type, and universally closed. -/
@[stacks 03ZM] #check (AlgebraicGeometry.AlgebraicSpace.Proper :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)
