/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap83.Definition_83_5_1_Orbit
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
variable (P : PreRelation U) (u : Points U.left)

/- Definition 83.5.1: for a pre-relation `j : R ⟶ U ⨯ U` over `B`, the `R`-orbit of
`u ∈ |U|` is the set `O_u ⊂ |U|` of points joined to `u` by a finite chain of length
`n ≥ 1` whose consecutive steps are equality or an `|R|`-edge in either the `s` or the
`t` direction. -/
@[stacks 048N] #check (PreRelation.pointsOrbit P u : Set (Points U.left))
