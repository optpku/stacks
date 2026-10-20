/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.IsoComma
public import stacks_project.Chap78.Lemma_78_20_2_Atlas
public import stacks_project.Chap78.Lemma_78_21_1_QuotientMap
public import stacks_project.Chap78.Lemma_78_21_2_IsoComma

universe u

/- The canonical two-commutative quotient-stack square of the iso-comma groupoid. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.isoCommaCone :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    {G H : AlgebraicGeometry.GroupoidAlgebraicSpace B}
    (f : AlgebraicGeometry.GroupoidAlgebraicSpace.Hom G H),
    CategoryTheory.Bicategory.PseudoPullbackCone
      (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.isoCommaConeRight f)
      (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.isoCommaConeBottom f))
