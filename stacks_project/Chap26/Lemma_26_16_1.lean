/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section

open AlgebraicGeometry CategoryTheory.Limits

/- Lemma 26.16.1: schemes have finite limits, hence a final object,
products, and fibre products. -/
@[stacks 01JM] #check (inferInstance : HasFiniteLimits Scheme)
