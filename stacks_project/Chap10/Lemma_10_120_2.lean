/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Span
import StacksCheckRecall

/-!
# Associated Elements and Principal Ideals

@stack 034Q
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R] [IsDomain R] {x y : R}

/- Lemma 10.120.2 (Stacks `034Q`): two elements of a domain are associated exactly when
their principal ideals agree. -/
@[stacks 034Q]
#check ((Ideal.span_singleton_eq_span_singleton (x := x) (y := y)).symm :
  Associated x y ↔ Ideal.span ({x} : Set R) = Ideal.span ({y} : Set R))
