module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Definition 71.10.6
Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`. We say
that pullbacks of meromorphic functions are defined for `f` if for every commutative
diagram with `U ∈ X_étale` and `V ∈ Y_étale` and any section `s ∈ S_Y(V)` the pullback
`f♯(s) ∈ 𝒪_X(U)` is an element of `S_X(U)`. -/
@[stacks 0EN8] #check
  (AlgebraicGeometry.AlgebraicSpace.PullbacksMeromorphicFunctionsDefined :
    {S : Scheme.{u}} → {X Y : AlgebraicGeometry.AlgebraicSpace S} → (X ⟶ Y) → Prop)
