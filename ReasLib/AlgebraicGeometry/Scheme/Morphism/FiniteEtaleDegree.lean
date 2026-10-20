/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X S : Scheme.{u}}

/-- A finite étale morphism `f : X ⟶ S` has constant degree prime to `ℓ` if it
is finite locally free of some rank `d` with `Nat.Coprime d ℓ`. -/
def IsConstantDegreePrimeTo (f : X ⟶ S) (ℓ : ℕ) : Prop :=
  ∃ d : ℕ, Nat.Coprime d ℓ ∧ IsFiniteLocallyFreeOfRank f d

/-- Constant degree prime to `ℓ` means some finite locally free rank coprime to `ℓ`. -/
theorem isConstantDegreePrimeTo_iff (f : X ⟶ S) (ℓ : ℕ) :
    IsConstantDegreePrimeTo f ℓ ↔
      ∃ d : ℕ, Nat.Coprime d ℓ ∧ IsFiniteLocallyFreeOfRank f d := sorry

end AlgebraicGeometry.Scheme.FiniteEtale

end
