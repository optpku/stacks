module

public import stacks_project.Chap73.Definition_73_8_6_Site
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 73.8.6: let `S` be a scheme. Let `(Spaces / S)_ph` be as in
Definition 73.8.5. Let `X` be an algebraic space over `S`, i.e. an object of
`(Spaces / S)_ph`. Then the big ph site `(Spaces / X)_ph` of `X` is the
localization of the site `(Spaces / S)_ph` at `X` introduced in Sites,
Section 7.25, recorded by `overPhTopology X`. -/
@[stacks 0DFL] #check AlgebraicGeometry.AlgebraicSpace.overPhTopology

#check CategoryTheory.GrothendieckTopology.over

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigPhSite
