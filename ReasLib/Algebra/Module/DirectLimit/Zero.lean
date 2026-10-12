/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Colimit.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Eventual vanishing in a directed module colimit

@stack 00D7

The direct-limit carrier in Mathlib is indexed by an explicit `DecidableEq I`; exposing that
instance parameter keeps the canonical quotient model visible and avoids a hidden classical pin.
-/

@[expose] public section

open Module.DirectLimit

universe u v w

namespace Module.DirectLimit

variable {R : Type u} [Semiring R]
variable {I : Type v} [Preorder I] [IsDirectedOrder I] [DecidableEq I]
variable (M : I → Type w) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable (μ : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable [DirectedSystem M (μ · · ·)]

/-- Lemma 10.8.4 (Tag 00D7): a stage element is zero in a directed module colimit exactly when
it becomes zero at a later stage. -/
@[stacks 00D7 "eventual zero criterion"]
theorem stageMap_eq_zero_iff {i : I} {x : M i} :
    of R I M μ i x = 0 ↔ ∃ (j : I) (hij : i ≤ j), μ i j hij x = 0 := by
  constructor
  · exact of.zero_exact
  · rintro ⟨j, hij, hx⟩
    rw [← of_f (R := R) (ι := I) (G := M) (f := μ) (i := i) (j := j)
      (hij := hij) (x := x), hx, map_zero]

end Module.DirectLimit
