module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PhPrecoverage.Over
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 73.8.6: let `S` be a scheme. Let `(Spaces / S)_ph` be as in
Definition 73.8.5. Let `X` be an algebraic space over `S`, i.e. an object of
`(Spaces / S)_ph`. Then the big ph site `(Spaces / X)_ph` of `X` is the
localization of the site `(Spaces / S)_ph` at `X` introduced in Sites,
Section 7.25. The Grothendieck-topology realization of this localization in
the inherited fixed-universe site presentation is `overPhTopology X`. -/
@[stacks 0DFL] #check (AlgebraicGeometry.AlgebraicSpace.overPhTopology :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.GrothendieckTopology (CategoryTheory.Over X))

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigPhSite.over_eq :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (J : AlgebraicGeometry.AlgebraicSpace.ChosenBigPhSite S)
    (X : AlgebraicGeometry.AlgebraicSpace S),
    J.toGrothendieck.over X = AlgebraicGeometry.AlgebraicSpace.overPhTopology X)
