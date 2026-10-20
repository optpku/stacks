/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap53.Lemma_53_18_1_GeometricGenus
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 53.18.1: the geometric genus of a proper scheme of dimension at most one is the
sum of the geometric genera of its reduced one-dimensional irreducible components. -/
@[stacks 0CE1] #check
  (AlgebraicGeometry.GeometricGenus.eq_finsum_irreducibleComponents :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
      AlgebraicGeometry.GeometricGenus.ofScheme X hdim =
        ∑ᶠ Z : irreducibleComponents X.left,
          if hZ : topologicalKrullDim
              (X.left.irreducibleComponentSubscheme Z) = 1 then
            AlgebraicGeometry.GeometricGenus.ofScheme
              (AlgebraicGeometry.SchemeOverField.oneDimensionalComponent X Z hZ) hZ.le
          else 0)
