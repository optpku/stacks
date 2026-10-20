module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Smooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 94.16.4: a groupoid `(U, R, s, t, c)` in algebraic spaces over an
algebraic space `B` over a scheme `S` is a smooth groupoid if `s, t : R ⟶ U`
are smooth morphisms of algebraic spaces. -/
@[stacks 04TH] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.Smooth :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}, GroupoidAlgebraicSpace B → Prop)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Smooth.iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
    GroupoidAlgebraicSpace.Smooth G ↔
      AlgebraicSpace.Smooth G.s.left ∧ AlgebraicSpace.Smooth G.t.left)
