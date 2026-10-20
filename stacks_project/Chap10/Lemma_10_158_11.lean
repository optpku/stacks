/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Separable.Generated.SmoothSubalgebra
public import ReasLib.RingTheory.CompleteIntersection.OverField.Approximation
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.158.11 [stacks 07BV]: canonical recall of the directed
approximation of field extensions by complete-intersection and, under
separability, smooth subalgebras.

@stack 07BV
-/

@[stacks 07BV "(1)"]
#check @IsGlobalCompleteIntersection.exists_directed_subalgebra_family

@[stacks 07BV "(2)"]
#check @Algebra.IsSeparableOver.exists_directed_smooth_subalgebra_family
