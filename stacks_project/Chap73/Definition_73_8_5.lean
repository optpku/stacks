module

public import stacks_project.Chap73.Definition_73_8_5_Site
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 73.8.5: let `S` be a scheme. A big ph site `(Spaces / S)_ph`
is any site constructed as follows: choosing a big ph site `(Sch / S)_ph`
is recorded by the universe of `Scheme` and `AlgebraicSpace S`; the underlying
category is `AlgebraicSpace S`; the coverings are a set of ph covering
families chosen by `Precoverage.exists_cardinalLE_site` from
`phPrecoverage`, i.e. a value of `ChosenBigPhSite S`. -/
@[stacks 0DFK] #check AlgebraicGeometry.AlgebraicSpace.ChosenBigPhSite

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.ofBound

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.spec

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigPhSite.exists

#check AlgebraicGeometry.AlgebraicSpace.phPrecoverage
