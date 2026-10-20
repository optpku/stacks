/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.CountablyGenerated.Basic

@[expose] public section

/-!
# Direct-sum Devissages

This file defines ordinal-indexed direct-sum devissages independently of any particular
application to projective modules. The countable-generation predicates and the internal-direct-sum
existence predicate live in `ReasLib.Algebra.Module.CountablyGenerated.Basic`.
-/

open scoped Ordinal
open Order

universe u v w

section DirectSumDevissage

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Definition 10.84.1 (Tag 058U): a direct sum devissage of an `R`-module `M` is an
ordinal-indexed increasing family of submodules starting at `0`, exhausting `M`, continuous at
limit ordinals, and such that each successor stage is a direct summand of the next stage. -/
@[stacks 058U]
structure DirectSumDevissage (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    where
  length : Ordinal.{w}
  length_pos : 0 < length
  stages : Ordinal.{w} →o Submodule R M
  stage_zero : stages 0 = ⊥
  iSup_stages : (⨆ α : Set.Iio length, stages α.1) = ⊤
  stage_limit :
    ∀ {α : Ordinal.{w}}, α < length → IsSuccLimit α → stages α = ⨆ β : Set.Iio α, stages β.1
  stage_succ_isCompl :
    ∀ {α : Ordinal.{w}}, α + 1 < length →
      ∃ q : Submodule R (stages (α + 1)),
        IsCompl ((stages α).comap (stages (α + 1)).subtype) q

namespace DirectSumDevissage

variable (D : DirectSumDevissage R M)

/-- The stage family of a direct sum devissage is increasing. -/
theorem monotone_stages : Monotone D.stages := sorry

/-- A stage can only increase along the ordinal indexing order. -/
theorem stages_le {α β : Ordinal.{w}} (h : α ≤ β) : D.stages α ≤ D.stages β := sorry

/-- The predecessor stage, viewed as a submodule of the corresponding successor stage. -/
abbrev predecessorStage (α : Ordinal.{w}) :
    Submodule R (D.stages (α + 1)) :=
  (D.stages α).comap (D.stages (α + 1)).subtype

/-- The continuity equation at a limit stage of a direct sum devissage. -/
theorem stage_limit_eq_iSup {α : Ordinal.{w}} (hα : α < D.length) (hlimit : IsSuccLimit α) :
    D.stages α = ⨆ β : Set.Iio α, D.stages β.1 := sorry

/-- A successor stage has a complement to its predecessor, in the successor-stage module. -/
theorem exists_predecessorStage_isCompl {α : Ordinal.{w}} (hα : α + 1 < D.length) :
    ∃ q : Submodule R (D.stages (α + 1)), IsCompl (D.predecessorStage α) q := sorry

/-- A direct sum devissage is Kaplansky if every successor quotient is countably generated. -/
@[stacks 058U "Kaplansky devissage"]
def IsKaplansky : Prop :=
  ∀ ⦃α : Ordinal.{w}⦄, α + 1 < D.length →
    Module.CountablyGenerated R (D.stages (α + 1) ⧸ D.predecessorStage α)

/-- The explicit successor-quotient formulation of `DirectSumDevissage.IsKaplansky`. -/
theorem isKaplansky_iff :
    D.IsKaplansky ↔ ∀ ⦃α : Ordinal.{w}⦄, α + 1 < D.length →
      Module.CountablyGenerated R (D.stages (α + 1) ⧸ D.predecessorStage α) := sorry

end DirectSumDevissage

end DirectSumDevissage
