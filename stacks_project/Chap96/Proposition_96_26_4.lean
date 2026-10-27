/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.Representable

/-!
# Quasi-coherent derived objects on a representable category fibred in groupoids
-/

@[expose] public section

universe u

/- Proposition 96.26.4: let `S` be a scheme and let `𝒳 → (Sch/S)_fppf` be a
category fibred in groupoids representable by an algebraic space `X`. Then
`QC(𝒳)` is canonically equivalent to `D_QCoh(𝒪_X)`.
In the enlarged affine presentation, `SmallQC` imposes sectionwise `u`-small
cohomology, matching the effective module universe `u` of the target. -/
@[stacks 0H0K]
#check (AlgebraicGeometry.GroupoidsOver.qcEquivalence :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (F : AlgebraicGeometry.AlgebraicSpace S)
    (X : AlgebraicGeometry.GroupoidsOver S)
    (e : CategoryTheory.Bicategory.Equivalence F.toGroupoids X),
    CategoryTheory.RLinear.TriangulatedEquivalence ℤ
      (AlgebraicGeometry.GroupoidsOver.SmallQC X)
      (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh F))
