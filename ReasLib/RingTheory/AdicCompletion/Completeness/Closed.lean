/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Completeness.Submodule
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.List.TFAE

@[expose] public section

universe u v

namespace Submodule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Closure in the genuine adic module topology is the positive-power
intersection. This needs no finite generation hypothesis. -/
theorem isClosed_adic_iff_iInf (N : Submodule R M) (I : Ideal R) :
    @IsClosed M (I.adicModuleTopology M) (N : Set M) ↔
      N = ⨅ n : ℕ+, N ⊔ I ^ (n : ℕ) • (⊤ : Submodule R M) := sorry

/-- For a complete ambient module, closedness, the positive-power intersection
criterion, and adic completeness of the quotient are equivalent. -/
theorem closed_adic_complete_quotient_tfae (N : Submodule R M) (I : Ideal R)
    [IsAdicComplete I M] :
    List.TFAE [
      @IsClosed M (I.adicModuleTopology M) (N : Set M),
      N = ⨅ n : ℕ+, N ⊔ I ^ (n : ℕ) • (⊤ : Submodule R M),
      IsAdicComplete I (M ⧸ N)
    ] := sorry

/-- A closed submodule of an adically complete module is adically complete
when the ideal is finitely generated. -/
theorem isAdicComplete_of_isClosed_adic (N : Submodule R M) (I : Ideal R)
    [IsAdicComplete I M] (hI : I.FG)
    (hN : @IsClosed M (I.adicModuleTopology M) (N : Set M)) :
    IsAdicComplete I N := sorry

end Submodule
