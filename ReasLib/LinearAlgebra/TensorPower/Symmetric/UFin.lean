/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorPower.Symmetric

@[expose] public section

/-!
# Universe-lifted finite index types for symmetric tensor powers

`SymmetricPower.UFin n` is the finite index type `Fin n` lifted to the universe required by
mathlib's symmetric tensor power construction.
-/

namespace SymmetricPower

universe u

/-- The finite index type `Fin n` lifted to the universe of the coefficient ring. -/
abbrev UFin (n : ℕ) : Type u := ULift.{u} (Fin n)

end SymmetricPower
