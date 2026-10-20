/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Separable.Generated.SmoothSubalgebra
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.158.10 [stacks 037X]: canonical recall of the smooth
fraction-field model criterion for an essentially finite-type field extension.

@stack 037X
-/

@[stacks 037X]
#check @Algebra.IsSeparableOver.iff_exists_smooth_subalgebra_isFractionRing
