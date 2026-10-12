/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap83.Definition_83_5_1_Orbit

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}

/-- Lemma 83.5.2: if `P` is a pre-equivalence relation of algebraic spaces over `B`,
then the `R`-orbit of a point `u` of `|U|` equals the set of points `u'` of `|U|`
for which there exists `r` of `|R|` with `Points.map P.s.left r = u` and
`Points.map P.t.left r = u'`. -/
@[stacks 048O]
theorem pointsOrbit_eq_of_isPreEquivalence (P : PreRelation U) (hP : P.IsPreEquivalence)
    (u : Points U.left) :
    P.pointsOrbit u =
      {u' | ∃ r : Points P.left.left, Points.map P.s.left r = u ∧ Points.map P.t.left r = u'} :=
  sorry

/-- Membership in the `R`-orbit of `u` under a pre-equivalence relation is equivalent to
the existence of a point `r` of `|R|` with `Points.map P.s.left r = u` and
`Points.map P.t.left r = u'`. -/
theorem mem_pointsOrbit_of_isPreEquivalence (P : PreRelation U) (hP : P.IsPreEquivalence)
    (u u' : Points U.left) :
    u' ∈ P.pointsOrbit u ↔
      ∃ r : Points P.left.left, Points.map P.s.left r = u ∧ Points.map P.t.left r = u' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
