module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfPrecoverage.ChosenSite
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 73.7.6: let `S` be a scheme. A big fppf site `(Spaces / S)_fppf`
is any site constructed as follows: choosing a big fppf site `(Sch / S)_fppf`
is recorded by the established ambient model of `AlgebraicSpace S`; the
underlying category is `AlgebraicSpace S`. The selected set-indexed fppf
coverings satisfy both index-cardinality and family-code rank bounds, as in
Sets Lemma 3.11.1 and `SetIndexedFamily.exists_cardinalRank_site`, and form a
site combinatorially representing every ambient fppf covering. -/
@[stacks 0DBV] #check (AlgebraicGeometry.AlgebraicSpace.ChosenBigFppfSite :
  AlgebraicGeometry.Scheme.{u} → Type (u + 2))

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigFppfSite.ofBounds

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigFppfSite.coverings

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigFppfSite.mem_coverings_iff

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigFppfSite.precoverage

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigFppfSite.toGrothendieck

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigFppfSite.spec

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigFppfSite.exists
