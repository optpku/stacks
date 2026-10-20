/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Equiv.Basic
public import ReasLib.RingTheory.Flatness.MittagLeffler

@[expose] public section

/-!
# Mittag-Leffler Modules and Linear Equivalences

The Mittag-Leffler property is invariant under linear equivalence.  This leaf mirrors the
`Module.Flat.of_linearEquiv` and `Module.Flat.equiv_iff` API from Mathlib.
-/

universe u v w

namespace Module.MittagLeffler

variable {R : Type u} [Ring R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A module linearly equivalent to a Mittag-Leffler module is Mittag-Leffler. -/
@[stacks 059F "Mittag-Leffler invariance under linear equivalence"]
theorem of_linearEquiv [MittagLeffler R M] (e : N ≃ₗ[R] M) : MittagLeffler R N := sorry

/-- Linear equivalence preserves and reflects the Mittag-Leffler property. -/
theorem equiv_iff (e : M ≃ₗ[R] N) : MittagLeffler R M ↔ MittagLeffler R N := sorry

end Module.MittagLeffler
