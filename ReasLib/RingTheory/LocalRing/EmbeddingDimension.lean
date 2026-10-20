/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.Quotient

@[expose] public section

/-!
# Embedding Dimension of Local-Ring Quotients

This leaf records the elementary cotangent-space consequences of killing a
maximal-ideal element outside its square.  The statements are independent of
regular-locality; regular-local quotient consequences belong to
`RegularLocalRing.Quotient`.
-/

universe u

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A Noetherian local ring has positive embedding dimension exactly when its
maximal ideal contains an element outside its square. -/
@[stacks 07DX "positive embedding dimension and cotangent directions"]
theorem spanFinrank_pos_iff_exists_not_mem_sq :
    0 < (maximalIdeal R).spanFinrank ↔
      ∃ x : maximalIdeal R, (x : R) ∉ maximalIdeal R ^ 2 := sorry

/-- An element of the maximal ideal outside its square forces positive
embedding dimension. -/
@[stacks 07DX "positive embedding dimension from a cotangent direction"]
theorem spanFinrank_pos_of_not_mem_sq (x : maximalIdeal R)
    (hx : (x : R) ∉ maximalIdeal R ^ 2) :
    0 < (maximalIdeal R).spanFinrank := sorry

/-- Positive embedding dimension produces a maximal-ideal element outside the
square of the maximal ideal. -/
@[stacks 07DX "cotangent direction from positive embedding dimension"]
theorem exists_not_mem_sq_of_spanFinrank_pos
    (hpos : 0 < (maximalIdeal R).spanFinrank) :
    ∃ x : maximalIdeal R, (x : R) ∉ maximalIdeal R ^ 2 := sorry

/-- Killing a maximal-ideal element with nonzero cotangent class strictly
lowers the embedding dimension. -/
@[stacks 07DX "embedding dimension drops after a cotangent direction quotient"]
theorem spanFinrank_quotient_span_singleton_lt_of_not_mem_sq
    (x : maximalIdeal R) (hx : (x : R) ∉ maximalIdeal R ^ 2) :
    (maximalIdeal (R ⧸ Ideal.span ({(x : R)} : Set R))).spanFinrank <
      (maximalIdeal R).spanFinrank := sorry

end IsLocalRing
