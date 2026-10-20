/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.QuasiRegular.Basic

/-!
# Quasi-Regular Sequences and Linear Equivalences

Quasi-regularity depends only on the module up to linear equivalence.
-/

@[expose] public section

universe u v w

namespace RingTheory.Sequence.IsQuasiRegular

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Linearly equivalent modules have the same quasi-regular sequences. -/
@[stacks 065L "linear-equivalence invariance"]
theorem linearEquiv_iff {rs : List R} (e : M ≃ₗ[R] N) :
    IsQuasiRegular M rs ↔ IsQuasiRegular N rs := sorry

end RingTheory.Sequence.IsQuasiRegular
