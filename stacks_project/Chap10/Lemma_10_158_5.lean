/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Separable.FormallySmooth
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.158.5 [stacks 031Y]: canonical recall of the field-extension
bridge from formal smoothness to Stacks-project separability.

@stack 031Y
-/

@[stacks 031Y]
#check @Algebra.isSeparableOver_of_formallySmooth
