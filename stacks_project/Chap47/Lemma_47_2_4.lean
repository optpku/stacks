/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Submodule.Essential
import StacksCheckRecall

@[expose] public section

universe u v

variable {R : Type u} {N : Type v} [CommRing R] [AddCommGroup N] [Module R N]
variable (M : Submodule R N)

/- Lemma 47.2.4: A submodule `M` of an `R`-module `N` meets every nonzero submodule
nontrivially if and only if every nonzero `x : N` has a nonzero scalar multiple in `M`. -/
@[stacks 08XM] #check
  (Submodule.essential_iff_exists_smul_mem M :
    (∀ P : Submodule R N, P ≠ ⊥ → M ⊓ P ≠ ⊥) ↔
      ∀ x : N, x ≠ 0 → ∃ r : R, r • x ∈ M ∧ r • x ≠ 0)
