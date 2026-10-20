/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Countable.Basic
public import ReasLib.RingTheory.Flatness.LocallyFree

@[expose] public section

universe u v

namespace Module

/-- There exists a countable commutative ring with a projective module that is an internal direct
sum of countably many finite locally free rank-1 modules but is not locally free. -/
theorem exists_countable_projective_directSum_rankOne_not_locallyFree :
    ∃ (R : Type u) (_ : CommRing R) (_ : Countable R) (M : Type v)
      (_ : AddCommGroup M) (_ : Module R M) (L : ℕ → Submodule R M),
      Projective R M ∧ iSupIndep L ∧ iSup L = ⊤ ∧
        (∀ n, FiniteLocallyFreeOfRank R (L n) 1) ∧ ¬ LocallyFree R M := sorry

end Module
