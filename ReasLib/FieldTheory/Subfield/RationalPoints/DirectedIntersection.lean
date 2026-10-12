/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Subfield.RationalPoints
import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed intersections of rational points

@stack 07P3

For a finite coordinate type, nonzero rational points of a `K`-submodule descend through a
nonempty downward-directed family of subfields.  The finite index is a genuine hypothesis of the
descent statement; the coordinate construction itself is intentionally available without it.
-/

@[expose] public section

universe u v w

namespace Submodule.RationalPoints

variable {K : Type u} [Field K]
variable {A : Type v} {ι : Type w} [Finite ι]

/-- Rational points are nonzero over an infimum exactly when they are nonzero over every member of
a nonempty downward-directed family. -/
@[stacks 07P3 "directed intersection of rational points"]
theorem ne_bot_iff_iInf (h_nonempty : Nonempty A) (V : Submodule K (ι → K))
    (Kα : A → Subfield K) (h_directed : Directed (· ≥ ·) Kα) :
    V.rationalPoints (⨅ α, Kα α) ≠ ⊥ ↔
      ∀ α, V.rationalPoints (Kα α) ≠ ⊥ := sorry
-- Proof strategy: choose a finite enumeration of `ι`, run the coordinate induction from the
-- source descent argument, and use `Subfield.mem_iInf` to identify the descended coordinates.

/-- The directed-intersection criterion after naming its intersection subfield. -/
@[stacks 07P3 "directed intersection with named base"]
theorem ne_bot_iff_of_eq_iInf (h_nonempty : Nonempty A) (V : Submodule K (ι → K))
    (k : Subfield K) (Kα : A → Subfield K) (h_inter : k = ⨅ α, Kα α)
    (h_directed : Directed (· ≥ ·) Kα) :
    V.rationalPoints k ≠ ⊥ ↔ ∀ α, V.rationalPoints (Kα α) ≠ ⊥ := sorry
-- Proof strategy: rewrite `h_inter` and apply `ne_bot_iff_iInf`; no new finite-coordinate
-- argument is needed in this source-facing bridge.

/-- Lemma 15.46.3 (nonzero-vector form): a finite-coordinate subspace has a nonzero vector over
the intersection subfield exactly when each member of the directed family has one. -/
@[stacks 07P3 "directed intersection nonzero-vector form"]
theorem exists_ne_zero_iff_of_eq_iInf (h_nonempty : Nonempty A) (V : Submodule K (ι → K))
    (k : Subfield K) (Kα : A → Subfield K) (h_inter : k = ⨅ α, Kα α)
    (h_directed : Directed (· ≥ ·) Kα) :
    (∃ v ∈ V.rationalPoints k, v ≠ 0) ↔
      ∀ α, ∃ v ∈ V.rationalPoints (Kα α), v ≠ 0 := sorry
-- Proof strategy: convert each side with `Submodule.ne_bot_iff`, then use
-- `ne_bot_iff_of_eq_iInf`; the coordinate carrier and its membership API remain unchanged.

end Submodule.RationalPoints
