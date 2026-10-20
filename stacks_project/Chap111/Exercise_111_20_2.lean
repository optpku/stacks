/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.FieldTheory.Transcendence.Growth

universe u v

namespace Algebra

/- Exercise 111.20.2 (1) -/
@[stacks 0CVP] #check (Algebra.exists_submodule_pow_rank_growth :
    ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
      [Algebra.EssFiniteType k K],
      ∃ V : Submodule k K, FiniteDimensional k V ∧
        ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
          (n ^ Cardinal.toNat (trdeg k K) : Cardinal) ≤
            C * Module.rank k (V ^ n : Submodule k K))

/- Exercise 111.20.2 (2) -/
@[stacks 0CVP] #check (Algebra.submodule_pow_rank_le :
    ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
      [Algebra.EssFiniteType k K] (V : Submodule k K) [FiniteDimensional k V],
      ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        Module.rank k (V ^ n : Submodule k K) ≤
          (C * n ^ Cardinal.toNat (trdeg k K) : Cardinal))

/- Exercise 111.20.2 (3) -/
@[stacks 0CVP] #check (Algebra.trdeg_toNat_eq_sSup_pow_growth :
    ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
      [Algebra.EssFiniteType k K],
      Cardinal.toNat (trdeg k K) =
        sSup {e : ℕ | ∃ V : Submodule k K, FiniteDimensional k V ∧
          ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
            (n ^ e : Cardinal) ≤ C * Module.rank k (V ^ n : Submodule k K)})

/- Exercise 111.20.2 (4) -/
@[stacks 0CVP] #check (Algebra.trdeg_toNat_eq_sInf_pow_growth :
    ∀ {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
      [Algebra.EssFiniteType k K],
      Cardinal.toNat (trdeg k K) =
        sInf {e : ℕ | ∀ V : Submodule k K, FiniteDimensional k V →
          ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
            Module.rank k (V ^ n : Submodule k K) ≤
              (C * n ^ e : Cardinal)})

end Algebra
