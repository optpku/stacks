/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.StageMaps
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor vanishing along adic stage inclusions

This leaf owns the uniform, all-degree form of the ideal-power Tor vanishing statement.  The
map is the canonical `subtypeTorMap`; the derived tensor argument belongs to the proof layer and
does not appear in the public statement.

@stack 0FXN
@stack 0927
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IdealPower.Tor

variable {A : Type u} [CommRing A]

#synth HasProjectiveResolutions (ModuleCat.{u} A)

/-- The map on `Tor_p` induced by the inclusion of an adic stage is eventually zero. -/
@[stacks 0FXN "eventual adic-stage Tor vanishing"]
def EventuallyZero (I : Ideal A) (M N : ModuleCat A) (p : ℕ) : Prop :=
  ∃ c : ℕ, ∀ n, c ≤ n → subtypeTorMap I M N n p = 0

/-- A single positive adic stage kills the induced maps in every Tor degree. -/
@[stacks 0FXN "uniform all-degree adic-stage Tor vanishing"]
def UniformZero (I : Ideal A) (M N : ModuleCat A) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ p : ℕ, subtypeTorMap I M N n p = 0

/-- A uniform zero stage yields eventual vanishing in each fixed Tor degree. -/
@[stacks 0FXN "uniform Tor vanishing implies eventual vanishing"]
theorem UniformZero.eventuallyZero
    {I : Ideal A} {M N : ModuleCat A} (h : UniformZero I M N) (p : ℕ) :
    EventuallyZero I M N p := sorry

/-- Lemma 15.103.2 (0FXN): if `M` is finite and `I` annihilates `N`, one positive adic stage
annihilates the canonical maps on all `Tor_p(-, N)`. -/
@[stacks 0FXN "Lemma 15.103.2: uniform Tor vanishing"]
theorem UniformZero.of_annihilator
    [IsNoetherianRing A] (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]
    (hN : I ≤ Module.annihilator A N) :
    UniformZero I M N := sorry

/-- A power-annihilation hypothesis gives eventual vanishing of each fixed Tor map. -/
@[stacks 0927 "eventual Tor vanishing from power annihilation"]
theorem EventuallyZero.of_pow_le_annihilator
    [IsNoetherianRing A] (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]
    (p m : ℕ) (hN : I ^ m ≤ Module.annihilator A N) :
    EventuallyZero I M N p := sorry

end CategoryTheory.DerivedCategory.IdealPower.Tor
