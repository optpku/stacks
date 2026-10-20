/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness in positive chain degrees

This leaf isolates the degree-range predicate used by bounded chain-complex
arguments from any particular coordinate presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A chain complex is exact in every strictly positive degree. -/
@[stacks 00N1 "positive-degree exactness"]
def ExactInPositiveDegrees (K : ChainComplex C ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → K.ExactAt n

end ChainComplex
