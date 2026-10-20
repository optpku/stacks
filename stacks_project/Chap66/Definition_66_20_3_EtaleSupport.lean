/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.SectionSupport

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

/- The support of an abelian sheaf consists of the points with nonzero geometric stalk. -/
#check (AlgebraicGeometry.AlgebraicSpace.abelianSheafSupport :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    Sheaf (AlgebraicSpace.smallEtaleTopology X) AddCommGrpCat.{u + 1} →
      Set (AlgebraicSpace.Points X))

/- The support of a section is the closed complement of its largest vanishing open. -/
#check (AlgebraicGeometry.AlgebraicSpace.abelianSheafSectionSupport :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    (F : Sheaf (AlgebraicSpace.smallEtaleTopology X) AddCommGrpCat.{u + 1}) →
    (U : AlgebraicSpace.smallEtaleSite X) → F.obj.obj (op U) → Closeds U.left.left)
