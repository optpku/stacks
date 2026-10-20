/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Big
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage.ChosenSite
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 73.4.6: let `S` be a scheme. Let `(Spaces / S)_étale` be as in
Definition 73.4.5. Let `X` be an algebraic space over `S`, i.e. an object of
`(Spaces / S)_étale`. Then the big étale site `(Spaces / X)_étale` of `X` is
the localization of the site `(Spaces / S)_étale` at `X` introduced in Sites,
Section 7.25, recorded by `overEtaleTopology X`. The generated ambient topology
agrees with that of any admissible chosen big étale site. -/
@[stacks 0DBY] #check (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.GrothendieckTopology (CategoryTheory.Over X))

#check (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology_def :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X =
      AlgebraicGeometry.AlgebraicSpace.etaleTopology.over X)

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigEtaleSite :
  AlgebraicGeometry.Scheme.{u} → Type (u + 2))

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.toGrothendieck_eq :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {P : CategoryTheory.Precoverage (AlgebraicGeometry.AlgebraicSpace S)}
    (X : AlgebraicGeometry.AlgebraicSpace.ChosenBigSite P),
    X.toGrothendieck = P.toGrothendieck)
