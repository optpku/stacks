/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Functoriality
public import stacks_project.Chap78.Lemma_78_28_1_Quotient

/-!
# Morphisms of quotient stacks induced by morphisms of groupoids

The quotient-stack construction is provided by the shared functoriality owner.
This bridge retains the point-prestack presentation used by existing consumers.
-/

universe u

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.quotientStackMap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      {G H : AlgebraicGeometry.GroupoidAlgebraicSpace B},
      AlgebraicGeometry.GroupoidAlgebraicSpace.Hom G H →
        CategoryTheory.CartesianBasedFunctor
          (AlgebraicGeometry.GroupoidAlgebraicSpace.fppfQuotientStack G).p
          (AlgebraicGeometry.GroupoidAlgebraicSpace.fppfQuotientStack H).p)
