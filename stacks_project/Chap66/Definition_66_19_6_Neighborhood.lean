/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Neighborhood
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/- Small étale neighborhoods of a geometric point, with scheme domains in the small étale
site, are the category of lifts of that point. -/
#check (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtaleNeighborhood :
  AlgebraicSpace.GeometricPoint X → Type (u + 1))
