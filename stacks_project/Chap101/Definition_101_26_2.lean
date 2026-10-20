module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FlatAt
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 101.26.2: let `f : X ⟶ Y` be a morphism of algebraic stacks
and let `x` be a point of `Points X`. We say `f` is flat at `x` if the
equivalent conditions of Lemma 101.26.1 hold. -/
@[stacks 0CID] #check (AlgebraicGeometry.AlgebraicStack.existsFlatAtPointSquare :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (x : AlgebraicGeometry.AlgebraicStack.Points X), Prop)
