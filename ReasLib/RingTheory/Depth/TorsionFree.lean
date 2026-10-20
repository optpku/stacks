/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Free
public import ReasLib.RingTheory.Depth

@[expose] public section

universe u v

open IsLocalRing
open scoped ENat

namespace Module.IsTorsionFree

/-- A finite torsion-free module over a local Noetherian domain with nonzero maximal ideal has depth at least one. -/
theorem moduleDepth_ge_one {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
    [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] (h_maximalIdeal_ne_bot : maximalIdeal R ≠ ⊥) :
    (1 : ℕ∞) ≤ moduleDepth R M :=
  sorry

end Module.IsTorsionFree
