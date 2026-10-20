/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Data.Set.Countable
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Countably generated modules and internal direct sums

This foundational leaf owns the countable-generation predicates for submodules and modules, and
the existence predicate for an internal direct-sum decomposition into countably generated
submodules. It is independent of ordinal-indexed devissages and change of rings.
-/

universe u v x

section CountablyGenerated

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

namespace Submodule

/-- A submodule is countably generated if it is spanned by a countable subset. -/
@[stacks 05A7 "countably generated submodule"]
def CountablyGenerated (P : Submodule R M) : Prop :=
  ∃ s : Set M, s.Countable ∧ Submodule.span R s = P

/-- `Submodule.CountablyGenerated` means precisely that the submodule is spanned by a countable
subset. -/
theorem countablyGenerated_iff {P : Submodule R M} :
    P.CountablyGenerated ↔ ∃ s : Set M, s.Countable ∧ Submodule.span R s = P := sorry

/-- The span of a countable subset is countably generated. -/
theorem countablyGenerated_span {s : Set M} (hs : s.Countable) :
    (Submodule.span R s).CountablyGenerated := sorry

end Submodule

namespace Module

variable (R M)

/-- A module is countably generated if some countable subset spans it. -/
@[stacks 05A6 "countably generated module"]
def CountablyGenerated : Prop :=
  (⊤ : Submodule R M).CountablyGenerated

/-- `Module.CountablyGenerated` means precisely that the module is spanned by a countable subset. -/
theorem countablyGenerated_iff :
    Module.CountablyGenerated R M ↔
      ∃ s : Set M, s.Countable ∧ Submodule.span R s = (⊤ : Submodule R M) := sorry

namespace CountablyGenerated

/-- An `R`-module is the supremum of an independent family of countably generated submodules.
This is the canonical proposition-facing owner: unlike `DirectSum.IsInternal`, it does not require
a chosen `DecidableEq` instance on the index type. -/
@[stacks 05A3 "direct sum of countably generated submodules"]
def IsDirectSum : Prop :=
  ∃ (ι : Type x) (summand : ι → Submodule R M),
    iSupIndep summand ∧ iSup summand = ⊤ ∧ ∀ i, (summand i).CountablyGenerated

/-- Characterization of `Module.CountablyGenerated.IsDirectSum` by its independent summands,
spanning condition, and countable-generation condition. -/
theorem isDirectSum_iff :
    IsDirectSum.{u, v, x} R M ↔
      ∃ (ι : Type x) (summand : ι → Submodule R M),
        iSupIndep summand ∧ iSup summand = ⊤ ∧
          ∀ i, (summand i).CountablyGenerated := sorry

end CountablyGenerated

/-- Compatibility predicate using Mathlib's `DirectSum.IsInternal` packaging. New proposition-only
APIs should prefer `Module.CountablyGenerated.IsDirectSum`. -/
@[stacks 05A3 "direct sum of countably generated submodules"]
def IsDirectSumOfCountablyGenerated : Prop :=
  ∃ (ι : Type x) (_ : DecidableEq ι) (summand : ι → Submodule R M),
    DirectSum.IsInternal summand ∧ ∀ i, (summand i).CountablyGenerated

end Module

end CountablyGenerated

section InternalDirectSum

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Module

/-- `Module.IsDirectSumOfCountablyGenerated` records an internal direct-sum decomposition by
countably generated submodules. -/
theorem isDirectSumOfCountablyGenerated_iff :
    Module.IsDirectSumOfCountablyGenerated.{u, v, x} R M ↔
      ∃ (ι : Type x) (summand : ι → Submodule R M),
        iSupIndep summand ∧ iSup summand = ⊤ ∧ ∀ i, (summand i).CountablyGenerated := sorry

/-- The `DirectSum.IsInternal` compatibility predicate is equivalent to the canonical
proposition-facing direct-sum predicate. -/
theorem isDirectSumOfCountablyGenerated_iff_isDirectSum :
    Module.IsDirectSumOfCountablyGenerated.{u, v, x} R M ↔
      Module.CountablyGenerated.IsDirectSum.{u, v, x} R M := sorry

end Module

end InternalDirectSum
