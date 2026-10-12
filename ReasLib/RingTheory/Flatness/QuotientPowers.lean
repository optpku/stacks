/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness Along Ideal-Power Quotients

@stack 0523

This leaf owns the reusable predicate that every positive ideal-power quotient
of a module is flat over the matching quotient of its base ring.
-/

@[expose] public section

universe u v

namespace Module.Flat

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Flatness of all positive `I`-adic quotient stages of `M` over their
corresponding quotient rings. -/
@[stacks 0523 "flat quotients by ideal powers"]
abbrev QuotientPowers (I : Ideal R) : Prop :=
  ∀ n : ℕ, 1 ≤ n → Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M)))

end Module.Flat
