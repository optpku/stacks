/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Length
import StacksCheckRecall

@[expose] public section

universe u v

/- Exercise 111.9.2: a module `M` over a ring `R` has `Module.length R M = 1`
if and only if it is isomorphic to `R ⧸ m` for some maximal ideal `m` of `R`. -/
@[stacks 076F] #check (Module.length_eq_one_iff_quot_maximal :
  ∀ {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M],
    Module.length R M = 1 ↔
      ∃ m : Ideal R, m.IsMaximal ∧ Nonempty (M ≃ₗ[R] R ⧸ m))
