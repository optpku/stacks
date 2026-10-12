/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective covers of finite modules over local rings

This file records the existence of a finite free essential surjection onto a finite module over a
local ring.
-/

@[expose] public section

universe u v

namespace Module.Finite

/-- A finite module over a commutative local ring admits a finite free essential surjection. -/
@[stacks 08Y0]
theorem exists_fin_projectiveCover
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [IsLocalRing R] [Module.Finite R M] :
    ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M),
      f.range = ⊤ ∧ ∀ N : Submodule R (Fin n → R), N.map f = ⊤ → N = ⊤ := sorry

end Module.Finite
