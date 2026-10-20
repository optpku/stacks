/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.DFinsupp
public import ReasLib.RingTheory.Flatness.MittagLeffler.Equiv

/-!
# Direct sums of Mittag-Leffler modules

This file contains the retract and arbitrary direct-sum closure properties of
`Module.MittagLeffler`.  These statements only require a ring; commutativity is needed by some
tensor-product criteria, not by the closure properties themselves.
-/

@[expose] public section

open scoped DirectSum

universe u v w

namespace Module.MittagLeffler

variable {R : Type u} [Ring R]

/-- A linear retract of a Mittag-Leffler module is Mittag-Leffler. -/
theorem of_retract {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hN : MittagLeffler R N) (i : M →ₗ[R] N) (r : N →ₗ[R] M)
    (h : r.comp i = LinearMap.id) : MittagLeffler R M := sorry

variable {I : Type v} {M : I → Type w}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Lemma 10.89.10, tag `059P`: an arbitrary direct sum is Mittag-Leffler exactly when every
summand is Mittag-Leffler. -/
@[stacks 059P]
theorem directSum_iff :
    MittagLeffler R (⨁ i, M i) ↔ ∀ i, MittagLeffler R (M i) := sorry

/-- The `DFinsupp` formulation of `Module.MittagLeffler.directSum_iff`. -/
theorem dfinsupp_iff :
    MittagLeffler R (Π₀ i, M i) ↔ ∀ i, MittagLeffler R (M i) := sorry

/-- An arbitrary direct sum of Mittag-Leffler modules is Mittag-Leffler. -/
instance directSum [∀ i, MittagLeffler R (M i)] :
    MittagLeffler R (⨁ i, M i) := sorry

/-- A `DFinsupp` of Mittag-Leffler modules is Mittag-Leffler. -/
instance dfinsupp [∀ i, MittagLeffler R (M i)] :
    MittagLeffler R (Π₀ i, M i) := sorry

end Module.MittagLeffler
