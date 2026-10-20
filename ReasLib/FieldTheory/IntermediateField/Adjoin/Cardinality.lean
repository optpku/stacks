/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Data.Set.Countable

@[expose] public section

/-!
# Cardinality of adjoined intermediate fields

Cardinality consequences of generating an intermediate field from a small set.
-/

universe u v

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

/-- A countable family over a countable base field cannot generate an extension whose carrier is
uncountable. -/
theorem adjoin_ne_top_of_countable [Countable F]
    (hE : ¬ (Set.univ : Set E).Countable) {s : Set E} (hs : s.Countable) :
    adjoin F s ≠ ⊤ := sorry

end IntermediateField
