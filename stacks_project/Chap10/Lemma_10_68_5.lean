/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.Regularity.BaseChange
import StacksCheckRecall

/-!
# Lemma 10.68.5

@stack 00LM
-/

@[expose] public section

/-
Lemma 10.68.5 (Stacks tag `00LM`) is a chapter-facing recall of the
tensor-product owner.  The self-module specialization is available from the
same shared leaf when a downstream argument needs it.
-/
@[stacks 00LM]
#check @RingTheory.Sequence.IsRegular.iff_tensorProduct_of_flat_localHom

@[stacks 00LM "map-first regularity base change"]
#check @RingTheory.Sequence.IsRegular.iff_map_of_flat_localHom
