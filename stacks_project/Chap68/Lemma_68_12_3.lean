module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Separation
import StacksCheckRecall

/-!
# Decent algebraic spaces have Kolmogorov points

The space of points of a decent algebraic space is a Kolmogorov space, i.e. a
`T0Space`.
-/

@[expose] public section

universe u

/- Lemma 68.12.3: Let `S` be a scheme. Let `X` be a decent algebraic space over
`S`. Then `Points X` is Kolmogorov in the sense of Topology, Definition 5.8.6,
i.e. a `T0Space`. -/
@[stacks 03K3] #check (AlgebraicGeometry.AlgebraicSpace.instT0SpacePoints :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X],
    T0Space (AlgebraicGeometry.AlgebraicSpace.Points X))
