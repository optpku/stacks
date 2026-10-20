/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Projective
public import ReasLib.RingTheory.Finiteness.Projective.CountablyGenerated.Complement
import StacksCheckRecall

/-!
# Lemma 10.85.2

@stack 0591
-/

@[expose] public section

universe u v

/-! The numbered item is a canonical recall of the ReasLib owners below. -/

@[stacks 0591 "finite-free complement property"]
#check @Module.HasFiniteFreeComplementSummandProperty

@[stacks 0591 "countably generated projective modules are free"]
#check @Module.free_of_countablyGenerated_of_hasFiniteFreeComplementSummandProperty
