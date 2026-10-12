/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap73.Lemma_73_4_7_Relocalization
public import stacks_project.Chap73.Definition_73_4_5_Site
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 73.4.6: let `S` be a scheme. Let `(Spaces / S)_étale` be as in
Definition 73.4.5. Let `X` be an algebraic space over `S`, i.e. an object of
`(Spaces / S)_étale`. Then the big étale site `(Spaces / X)_étale` of `X` is
the localization of the site `(Spaces / S)_étale` at `X` introduced in Sites,
Section 7.25, recorded by `overEtaleTopology X`. -/
@[stacks 0DBY] #check AlgebraicGeometry.AlgebraicSpace.overEtaleTopology

#check CategoryTheory.GrothendieckTopology.over

#check AlgebraicGeometry.AlgebraicSpace.ChosenBigEtaleSite
