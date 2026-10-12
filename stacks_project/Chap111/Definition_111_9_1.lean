/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Length.Chain
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 111.9.1: the length of an arbitrary module is the supremum of the lengths
of finite strict submodule chains from the zero submodule to the whole module. -/
@[stacks 076E] #check (Module.length_eq_iSup_chainLengths :
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M],
    Module.length R M =
      ⨆ (n : ℕ) (_ : ∃ chain : Fin (n + 1) → Submodule R M,
        StrictMono chain ∧ chain 0 = ⊥ ∧ chain (Fin.last n) = ⊤), (n : ℕ∞))

/- The canonical module-length invariant takes values in ℕ∞. -/
#check (Module.length :
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M], ℕ∞)

/- Module length is also the coheight of the zero submodule. -/
#check (Module.length_eq_coheight :
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M],
    Module.length R M = Order.coheight (⊥ : Submodule R M))
