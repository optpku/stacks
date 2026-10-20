module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Orbit
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 83.5.2: if `P` is a pre-equivalence relation of algebraic spaces over `B`,
then the `R`-orbit of a point `u` of `|U|` equals the set of points `u'` of `|U|`
for which there exists `r` of `|R|` with `Points.map P.s.left r = u` and
`Points.map P.t.left r = u'`. -/
@[stacks 048O]
#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.pointsOrbit_eq_of_isPreEquivalence :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U),
    P.IsPreEquivalence → ∀ u : Points U.left,
      P.pointsOrbit u =
        {u' | ∃ r : Points P.left.left,
          Points.map P.s.left r = u ∧ Points.map P.t.left r = u'})

/- Membership in the `R`-orbit of `u` under a pre-equivalence relation is equivalent to
the existence of a point `r` of `|R|` with `Points.map P.s.left r = u` and
`Points.map P.t.left r = u'`. -/
#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.mem_pointsOrbit_of_isPreEquivalence :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U),
    P.IsPreEquivalence → ∀ u u' : Points U.left,
      u' ∈ P.pointsOrbit u ↔
        ∃ r : Points P.left.left,
          Points.map P.s.left r = u ∧ Points.map P.t.left r = u')
