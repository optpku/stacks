/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.TensorPower.Symmetric.UFin

@[expose] public section

open scoped TensorProduct

/-!
# Free symmetric tensor powers

This file supplies the free-module instances for symmetric tensor powers. The universe-polymorphic
instance uses the universe-adjusted index type `UFin n`; a `Fin n` bridge is available when the
coefficient ring lies in `Type`.
-/

namespace SymmetricPower

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A free module has free symmetric tensor powers indexed by `SymmetricPower.UFin n`. -/
noncomputable instance instFree [Module.Free R M] (n : ℕ) :
    Module.Free R (Sym[R] (UFin n) M) := sorry

end

section

variable {R : Type} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.13.1: a free module has free `Fin n`-indexed symmetric powers. -/
@[stacks 00DN]
noncomputable instance instFreeFin [Module.Free R M] (n : ℕ) :
    Module.Free R (Sym[R]^n M) := sorry

end

end SymmetricPower
