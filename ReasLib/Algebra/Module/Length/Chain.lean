/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Length

@[expose] public section

universe u v

namespace Module

/-- The length of a module is the supremum of the lengths of finite strictly increasing
chains of submodules beginning at the zero submodule and ending at the whole module. -/
theorem length_eq_iSup_chainLengths (R : Type u) (M : Type v)
    [Ring R] [AddCommGroup M] [Module R M] :
    Module.length R M =
      ⨆ (n : ℕ) (_ : ∃ chain : Fin (n + 1) → Submodule R M,
        StrictMono chain ∧ chain 0 = ⊥ ∧ chain (Fin.last n) = ⊤), (n : ℕ∞) := sorry

end Module
