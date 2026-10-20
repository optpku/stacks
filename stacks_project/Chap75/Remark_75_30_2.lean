/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap96.Proposition_96_26_4_Comparison

universe u

/- Remark 75.30.2: for a scheme `S` and an algebraic space `X` over `S`,
`QC((Aff/X), 𝒪) := GroupoidsOver.QC X.toGroupoids` is canonically equivalent
to `D_QCoh(𝒪_X)`. This is the identity-representable case of Sheaves on
Stacks, Proposition 96.26.4. -/
@[stacks 0H07]
#check
  (fun {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S) ↦
      @AlgebraicGeometry.GroupoidsOver.qcEquivalence S X X.toGroupoids
        (CategoryTheory.Bicategory.Equivalence.id X.toGroupoids) sorry sorry sorry :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
      CategoryTheory.RLinear.TriangulatedEquivalence ℤ
        (AlgebraicGeometry.GroupoidsOver.QC X.toGroupoids)
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X))
