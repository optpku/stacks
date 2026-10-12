/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite free resolutions of prescribed length

@stack 064P

This leaf owns the recursive module-theoretic predicate for a finite free resolution of a fixed
length. Derived-category characterizations and coherent-ring consequences belong in downstream
leaves.
-/

universe u v

namespace Module

/-- An `R`-module has a finite free resolution of length `n` when it is finite for `n = 0`, and
for `n + 1` it admits a surjection from a finite free module whose kernel has a resolution of
length `n`. -/
@[stacks 064P "finite free resolution of prescribed length"]
def HasLengthFiniteFreeResolution
    (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] : ℕ → Prop
  | 0 => Module.Finite R M
  | n + 1 =>
      ∃ (F : Type v) (_ : AddCommGroup F) (_ : Module R F),
        Module.Free R F ∧ Module.Finite R F ∧
          ∃ f : F →ₗ[R] M, Function.Surjective f ∧
            HasLengthFiniteFreeResolution R (LinearMap.ker f) n

/-- A successor-length finite free resolution consists of one finite free cover followed by a
resolution of its kernel of the preceding length. -/
@[stacks 064P "successor finite free resolution"]
theorem hasLengthFiniteFreeResolution_succ_iff
    (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    HasLengthFiniteFreeResolution R M (n + 1) ↔
      ∃ (F : Type v) (_ : AddCommGroup F) (_ : Module R F),
        Module.Free R F ∧ Module.Finite R F ∧
          ∃ f : F →ₗ[R] M, Function.Surjective f ∧
            HasLengthFiniteFreeResolution R (LinearMap.ker f) n := sorry

end Module
