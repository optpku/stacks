/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Stable ideals for invariant actions

This narrow leaf owns the action-level predicate used by quotient, prime-fiber, and residue-field
constructions.  Keeping it separate from quotient data lets downstream statements import only the
semantic predicate they need.
@stack 09EG
-/

universe u v

open scoped Pointwise

namespace Ideal

variable {R : Type u} {G : Type v} [Semiring R] [Group G] [MulSemiringAction G R]

/- The group is explicit because an ideal can be stable for one action and not for another. -/
/-- An ideal is stable under every element of the indicated group action. -/
@[stacks 09EG "stable ideal predicate"]
abbrev IsStable (I : Ideal R) (G : Type v) [Group G] [MulSemiringAction G R] : Prop :=
  ∀ g : G, g • I = I

/-- Stability is equivalent to containment in the ideal stabilizer subgroup. -/
@[stacks 09EG "stable ideal stabilizer criterion"]
theorem isStable_iff_le_stabilizer (I : Ideal R) :
    I.IsStable G ↔ (⊤ : Subgroup G) ≤ MulAction.stabilizer G I := sorry
-- Proof strategy: unfold `IsStable` and `SetLike.le_def`; membership in `⊤` is automatic, and
-- `MulAction.mem_stabilizer_iff` identifies the remaining condition with `g • I = I`.

/-- Stability under a subgroup is equivalent to containment in the ambient ideal stabilizer. -/
@[stacks 09EG "subgroup stability stabilizer criterion"]
theorem isStable_subgroup_iff_le_stabilizer
    (I : Ideal R) (H : Subgroup G) :
    I.IsStable H ↔ H ≤ MulAction.stabilizer G I := sorry
-- Proof strategy: unfold `IsStable` and `SetLike.le_def`; for `g : H`, reduce the restricted
-- action to the ambient action of `g.1`, then use `MulAction.mem_stabilizer_iff` in both directions.

end Ideal
