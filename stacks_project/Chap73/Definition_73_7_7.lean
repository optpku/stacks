module

public import stacks_project.Chap73.Definition_73_7_6_Site
public import Mathlib.CategoryTheory.Sites.Over
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} (𝒮 : ChosenBigFppfSite S) (X : AlgebraicSpace S)

/- Definition 73.7.7: let `S` be a scheme. Let `(Spaces / S)_fppf` be as in
Definition 73.7.6, recorded by a chosen site `𝒮`. Let `X` be an algebraic space
over `S`, i.e. an object of that site. Then the big fppf site `(Spaces / X)_fppf`
is the Sites 7.25 localization of `(Spaces / S)_fppf` at `X`, namely
`𝒮.toGrothendieck.over X`. -/
@[stacks 0DBW] #check (𝒮.toGrothendieck.over X : GrothendieckTopology (Over X))

#check GrothendieckTopology.over

#check GrothendieckTopology.mem_over_iff

#check ChosenBigSite.toGrothendieck

#check ChosenBigSite.toGrothendieck_eq

#check ((fppfPrecoverage S).toGrothendieck.over X : GrothendieckTopology (Over X))

#check over_toGrothendieck_eq_toGrothendieck_comap_forget
