/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Stalk
public import stacks_project.Chap66.Definition_66_19_6_Neighborhood

open CategoryTheory AlgebraicGeometry Opposite

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/- Stalks of presheaves are colimits of sections over the opposite category of small étale
neighborhoods of the geometric point. -/
#check (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.stalk :
  AlgebraicSpace.GeometricPoint X → ((AlgebraicSpace.smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) →
    Type (u + 1))
