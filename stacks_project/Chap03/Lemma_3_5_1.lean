/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.SetTheory.ZFC.VonNeumann
import StacksCheckRecall

@[expose] public section

universe u

open scoped ZFSet

/- Lemma 3.5.1: every set `x : ZFSet` is an element of `V_ o` for some ordinal `o`. -/
@[stacks 000C] #check
  (ZFSet.exists_mem_vonNeumann :
    ∀ x : ZFSet.{u}, ∃ ordinal : Ordinal.{u}, x ∈ V_ ordinal)
