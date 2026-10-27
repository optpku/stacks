/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Completeness.Closed
import StacksCheckRecall

@[expose] public section

universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma (0HB3) (1). For an I-adically complete module M, closedness of N,
the positive-power intersection criterion, and adic completeness of M ⧸ N
are equivalent. -/
@[stacks 0HB3] #check
  (Submodule.closed_adic_complete_quotient_tfae : ∀ (N : Submodule R M) (I : Ideal R)
    [IsAdicComplete I M],
    List.TFAE [
      @IsClosed M (I.adicModuleTopology M) (N : Set M),
      N = ⨅ n : ℕ+, N ⊔ I ^ (n : ℕ) • (⊤ : Submodule R M),
      IsAdicComplete I (M ⧸ N)
    ])

/- Lemma (0HB3) (2). If I is finitely generated, these equivalent conditions
also imply that N is I-adically complete. -/
@[stacks 0HB3] #check
  (Submodule.isAdicComplete_of_isClosed_adic : ∀ (N : Submodule R M) (I : Ideal R)
    [IsAdicComplete I M] (hI : I.FG)
    (hN : @IsClosed M (I.adicModuleTopology M) (N : Set M)),
    IsAdicComplete I N)
