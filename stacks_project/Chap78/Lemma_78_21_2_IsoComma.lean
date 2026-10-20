/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.IsoComma
public import stacks_project.Chap78.Definition_78_11_1_Groupoid

universe u

/- The iso-comma construction for a morphism of groupoids in algebraic spaces. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.isoComma :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    {G H : AlgebraicGeometry.GroupoidAlgebraicSpace B},
    AlgebraicGeometry.GroupoidAlgebraicSpace.Hom G H →
      AlgebraicGeometry.GroupoidAlgebraicSpace B)
