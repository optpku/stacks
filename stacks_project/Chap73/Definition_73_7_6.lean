module

public import stacks_project.Chap73.Definition_73_7_6_Site
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 73.7.6: let `S` be a scheme. A big fppf site `(Spaces / S)_fppf`
is any site constructed as follows: choosing a big fppf site `(Sch / S)_fppf`
is recorded by the universe of `Scheme` and `AlgebraicSpace S`; the underlying
category is `AlgebraicSpace S`; the coverings are a set of fppf covering
families chosen by `Precoverage.exists_cardinalLE_site` from
`fppfPrecoverage`, i.e. a value of `ChosenBigFppfSite S`. -/
@[stacks 0DBV] #check AlgebraicGeometry.AlgebraicSpace.ChosenBigFppfSite

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigFppfSite.ofCardinal

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.precoverage

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.toGrothendieck

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.spec

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigFppfSite.exists
