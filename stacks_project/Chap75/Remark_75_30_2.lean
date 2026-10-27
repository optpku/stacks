/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.Representable

universe u

/- Remark 75.30.2: for a scheme `S` and an algebraic space `X` over `S`,
`QC((Aff/X), 𝒪)` is canonically equivalent to `D_QCoh(𝒪_X)`.
The enlarged affine presentation uses `GroupoidsOver.SmallQC X.toGroupoids`,
whose sectionwise `u`-small cohomology matches the effective module universe `u`
of the native derived quasi-coherent category. -/
@[stacks 0H07]
#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.affineGroupoidsEquivalence :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.RLinear.TriangulatedEquivalence ℤ
      (AlgebraicGeometry.GroupoidsOver.SmallQC X.toGroupoids)
      (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X))
