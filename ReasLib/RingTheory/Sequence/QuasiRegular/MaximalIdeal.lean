/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.QuasiRegular.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-regular sequences in a local maximal ideal

Over a Noetherian local ring, a quasi-regular sequence contained in the maximal ideal is
regular on every nonzero finite module.
-/

@[expose] public section

universe u v

namespace RingTheory.Sequence.IsQuasiRegular

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A quasi-regular sequence in the maximal ideal of a Noetherian local ring is regular on
every nonzero finite module. -/
@[stacks 061S "quasi-regular sequence in the maximal ideal is regular"]
theorem isRegular_of_mem_maximalIdeal [Nontrivial M] {rs : List R}
    (hqr : IsQuasiRegular M rs)
    (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) :
    IsRegular M rs := sorry

end RingTheory.Sequence.IsQuasiRegular
