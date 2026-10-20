/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Separable.Generated.GeometricallyNormal
import StacksCheckRecall

@[expose] public section

/-!
# Geometric normality under separable base change

Lemma 10.165.6, tag `0C31`, is owned by the reusable separable-base-change
API for geometric normality.

@stack 0C31
-/

/- Lemma 10.165.6, tag `0C31`: geometric normality is unchanged after
restricting scalars along a separable algebraic field extension. -/
@[stacks 0C31]
#check @Algebra.IsGeometricallyNormal.iff_of_isSeparable
