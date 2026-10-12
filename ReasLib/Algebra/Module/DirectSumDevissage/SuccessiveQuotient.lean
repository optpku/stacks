/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DirectSumDevissage.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Successive quotients of a direct-sum dévissage

The complement chosen at a successor stage is not canonical.  This leaf therefore exposes only
the deterministic index and quotient types, together with the resulting existence theorem; a
chosen family of complements remains proof-local.
-/

open scoped DirectSum Ordinal

universe u v w

namespace DirectSumDevissage

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The ordinal indices of the successor stages of a direct-sum dévissage. -/
@[stacks 058V "successor-stage indices of a direct-sum devissage"]
abbrev successorIndex (D : DirectSumDevissage.{u, v, w} R M) : Type (w + 1) :=
  { α : Ordinal.{w} // α + 1 < D.length }

/-- The quotient contributed by a successor stage of a direct-sum dévissage. -/
@[stacks 058V "successive quotient of a direct-sum devissage"]
abbrev successiveQuotient (D : DirectSumDevissage.{u, v, w} R M)
    (α : D.successorIndex) : Type v :=
  D.stages (α.1 + 1) ⧸ D.predecessorStage α.1

/-- Lemma 10.84.2 (Tag 058V): a direct-sum dévissage decomposes its module as the direct sum of
the successive quotients.  The complement choices used to construct the equivalence are
non-canonical and are intentionally hidden behind this `Nonempty` statement. -/
@[stacks 058V "direct sum of successive quotients of a devissage"]
theorem nonempty_linearEquiv_successiveQuotients
    (D : DirectSumDevissage.{u, v, w} R M) :
    Nonempty (M ≃ₗ[R] ⨁ α : D.successorIndex, D.successiveQuotient α) := sorry

end DirectSumDevissage
