/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.JacobiZariski
import StacksCheckRecall

@[expose] public section

/-!
@stack 06A7
-/

/- Lemma 10.138.11 [stacks 06A7]: canonical recall of the split
surjective Jacobi-Zariski conormal sequence for a formally smooth map. -/

@[stacks 06A7]
#check @Algebra.H1Cotangent.delta_has_section_of_formallySmooth
