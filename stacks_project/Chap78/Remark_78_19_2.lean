/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.SpacesQuotient

@[expose] public section

universe u

/- Remark 78.19.2. The quotient on algebraic spaces and the original scheme-site
quotient over the base agree through their common sheafified fiber quotient. -/
@[stacks 044K] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.spacesFppfQuotient_agrees :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      {U : CategoryTheory.Over B} (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U),
      CategoryTheory.IsIso P.spacesFppfQuotientComparison ∧
        CategoryTheory.IsIso P.schemeFppfQuotientComparison)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.spacesFppfQuotientSheaf :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    {U : CategoryTheory.Over B} (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U),
    CategoryTheory.Sheaf
      ((AlgebraicGeometry.AlgebraicSpace.fppfPrecoverage S).toGrothendieck.over B)
      (Type (u + 1)))
