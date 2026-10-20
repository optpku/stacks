/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section

open AlgebraicGeometry CategoryTheory.Limits

/- Lemma 26.16.1: schemes have finite limits, hence a final object,
products, and fibre products. -/
@[stacks 01JM] #check (inferInstance : HasFiniteLimits Scheme)
