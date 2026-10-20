/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic
public import ReasLib.Algebra.Module.Length

@[expose] public section

universe u v

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The length of `M ⧸ I^n M` is the sum of the lengths of the first `n` associated-graded
pieces of the `I`-adic filtration. -/
theorem length_quotient_eq_sum (I : Ideal R) (n : ℕ) :
    Module.length R (M ⧸ (I ^ n • ⊤ : Submodule R M)) =
      ∑ p ∈ Finset.range n,
        Module.length R (Ideal.AssociatedGraded.piece I M p) := sorry

end Ideal.HilbertSamuel
