module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OnField
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Situation 79.9.2: here `S` is a scheme, `B` is an algebraic space, and
`(U, R, s, t, c)` is a groupoid in algebraic spaces over `B` with
`U = Spec(k)` for a field `k`. -/
@[stacks 06DY] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.IsOnField :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k], (Spec (.of k) ⟶ S) → Prop)
