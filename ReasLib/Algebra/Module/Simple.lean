module

public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Simple modules

The primitive owner is Mathlib's `IsSimpleModule`.  This leaf exposes the
source-friendly lattice formulation as a reusable bridge without introducing
a second predicate or a chapter dependency.

@stack 00J1
-/

universe u v

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-- A module is simple exactly when it is nontrivial and every submodule is
either `⊥` or `⊤`. -/
@[stacks 00J1 "simple module lattice criterion"]
theorem isSimpleModule_iff_nontrivial_and_submodule_eq_bot_or_eq_top :
    IsSimpleModule R M ↔
      Nontrivial M ∧ ∀ N : Submodule R M, N = ⊥ ∨ N = ⊤ := sorry
/- Proof strategy: rewrite with `isSimpleModule_iff`, then apply
`isSimpleOrder_iff` and `Submodule.nontrivial_iff`. -/
