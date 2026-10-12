/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap73.Definition_73_4_5_Site
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 73.4.5: let `S` be a scheme. A big étale site `(Spaces / S)_étale`
is any site constructed as follows: choosing a big étale site `(Sch / S)_étale`
is recorded by the universe of `Scheme` and `AlgebraicSpace S`; the underlying
category is `AlgebraicSpace S`; the coverings are a set of étale covering
families chosen by `Precoverage.exists_cardinalLE_site` from
`etalePrecoverage`, i.e. a value of `ChosenBigEtaleSite S`. -/
@[stacks 0DBX] #check AlgebraicGeometry.AlgebraicSpace.ChosenBigEtaleSite

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.ofBound

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.spec

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigEtaleSite.exists
