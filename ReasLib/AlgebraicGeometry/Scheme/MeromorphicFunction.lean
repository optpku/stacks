/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction

/-!
# Meromorphic functions on quasi-compact schemes

This file records the power-torsion behavior of global meromorphic functions that vanish on a
basic open of a quasi-compact scheme.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [CompactSpace X]

/-- A global meromorphic function on a quasi-compact scheme that vanishes on the basic open
defined by a regular function is annihilated by a power of that regular function. -/
@[stacks 08I7]
theorem exists_pow_mul_eq_zero_of_meromorphic_restrict_eq_zero
    (h : Γ(X, ⊤)) (f : X.toLocallyRingedSpace.meromorphicFunctions)
    (hf : f |_ₕ (homOfLE (X.basicOpen_le h)) = 0) :
    ∃ n : ℕ, (X.toLocallyRingedSpace.toMeromorphicFunctions h) ^ n * f = 0 := sorry

end AlgebraicGeometry
