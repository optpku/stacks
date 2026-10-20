/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Formal smoothness from a smooth presentation

@stack 00TM

Remark 10.138.6 is the general split-surjection criterion already owned by Mathlib.
-/

/- Remark 10.138.6: Lemma 10.138.5 extends from polynomial presentations to any surjective
`R`-algebra map `f : P →ₐ[R] A` whose source `P` is formally smooth over `R`. This is exactly the
canonical mathlib theorem `Algebra.FormallySmooth.iff_split_surjection`. -/
@[stacks 00TM]
#check @Algebra.FormallySmooth.iff_split_surjection
