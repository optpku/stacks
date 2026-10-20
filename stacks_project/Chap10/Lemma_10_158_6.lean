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
Lemma 10.158.6 [stacks 031Z]: canonical recall of the field criterion for
formal smoothness through first cotangent homology.

@stack 031Z
-/

@[stacks 031Z]
#check @Algebra.formallySmooth_iff_subsingleton_h1Cotangent_of_field
