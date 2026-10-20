/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap35.Lemma_35_23_10_Instances
import StacksCheckRecall

universe u

/- Lemma 35.23.10: the property `P(f)` given by “`f` is universally injective” is
fpqc local on the base. -/
@[stacks 02KW] #check (AlgebraicGeometry.UniversallyInjective.isLocalAtTargetFpqc :
  CategoryTheory.MorphismProperty.IsLocalAtTarget
    (@AlgebraicGeometry.UniversallyInjective :
      CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
    AlgebraicGeometry.Scheme.fpqcPrecoverage)
