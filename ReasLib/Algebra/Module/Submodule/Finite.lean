/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Basic
import StacksCheckRecall

/-!
# Finite Submodules

Mathlib already identifies finite modules with finitely generated top submodules and supplies the
specialization from a finite submodule to `Submodule.FG`.  This leaf is a stable recall surface for
those canonical owners; it deliberately introduces no parallel wrapper theorem.
-/

@[expose] public section

universe u v

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Submodule R M}

/- Stacks `052N`: the canonical proposition-level bridge from module finiteness to finite
generation. -/
@[stacks 052N "finite modules and finitely generated top submodules"] #check Module.Finite.fg_top

/- Companion recall: a finite submodule is finitely generated. -/
