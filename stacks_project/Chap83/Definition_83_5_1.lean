module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Orbit
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Definition 83.5.1: for a pre-relation `j : R ⟶ U ⨯ U` over `B`, the `R`-orbit of
`u ∈ |U|` is the set `O_u ⊂ |U|` of points joined to `u` by a finite chain of length
`n ≥ 1` whose consecutive steps are equality or an `|R|`-edge in either the `s` or the
`t` direction. -/
@[stacks 048N] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.pointsOrbit :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B},
      PreRelation U → Points U.left → Set (Points U.left))
