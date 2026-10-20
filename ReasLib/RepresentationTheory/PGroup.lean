/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Order.RelSeries
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

universe u v w

namespace Module

variable {Λ : Type u} {H : Type v} {M : Type w}

/-- A finitely generated module over the group algebra of a finite `ell`-group
over a commutative Noetherian ring, annihilated by `ell ^ n` with `1 ≤ n`, admits
a finite filtration whose successive quotients have trivial group action. -/
theorem existsFiniteTrivialActionFiltration
    [CommRing Λ] [IsNoetherianRing Λ]
    [Group H] [Finite H]
    [AddCommGroup M] [Module (MonoidAlgebra Λ H) M]
    [Module.Finite (MonoidAlgebra Λ H) M]
    (ell n : ℕ) [Fact (Nat.Prime ell)]
    (hn : 1 ≤ n) (hH : IsPGroup ell H)
    (h_ann : ∀ m : M, (ell ^ n) • m = 0) :
    ∃ s : RelSeries
        ({p : Submodule (MonoidAlgebra Λ H) M × Submodule (MonoidAlgebra Λ H) M |
          p.1 ≤ p.2 ∧
            ∀ h : H, ∀ x : p.2 ⧸ p.1.submoduleOf p.2,
              (MonoidAlgebra.single h (1 : Λ)) • x = x} : SetRel _ _),
      s.head = ⊥ ∧ s.last = ⊤ := sorry

end Module
