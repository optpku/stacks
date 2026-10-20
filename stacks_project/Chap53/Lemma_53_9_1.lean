/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.Principality

open Set TopologicalSpace

universe u

/- Lemma 53.9.1: if a closed subscheme of the projective plane over a field is
equidimensional of dimension one and has no embedded points (equivalently, it is
Cohen–Macaulay), then its corresponding homogeneous twist ideal is principal. -/
@[stacks 0BYB] #check
  (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.planeCurveTwistIdeal_isPrincipal :
    ∀ (k : Type u) [Field k]
      (Z : (AlgebraicGeometry.ProjectiveSpace.scheme k 2).IdealSheafData)
      (P : AlgebraicGeometry.ProjTwistPresentation
        (AlgebraicGeometry.ProjectiveSpace.grading k 2)),
      Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme) →
      (∀ C : irreducibleComponents Z.subscheme,
        topologicalKrullDim (C : Set Z.subscheme) = 1) →
      (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.twistIdeal 2 Z P).toIdeal.IsPrincipal)
