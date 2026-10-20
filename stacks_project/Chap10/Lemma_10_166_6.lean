/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.GeometricRegularity.Separable
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.166.6

@stack 07QH
-/

/- Lemma 10.166.6 [stacks 07QH]: canonical recall of invariance of geometric regularity
under a separable algebraic change of the base field. -/
@[stacks 07QH]
#check @Algebra.IsGeometricallyRegular.iff_of_isSeparable
