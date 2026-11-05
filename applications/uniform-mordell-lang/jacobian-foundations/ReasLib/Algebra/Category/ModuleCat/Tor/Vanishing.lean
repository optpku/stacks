module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Eventual vanishing of module Tor

This leaf names the bounded-vanishing conditions for the ordinary `Tor`
bifunctor. The predicates take bundled modules, so downstream statements do
not need local module structures or nested functor applications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ModuleCat.Tor

variable {R : Type u} [CommRing R]

/-- `Tor_p^R(M, N)` vanishes in every degree strictly above `n`. -/
@[stacks 09PX "Tor vanishing above a bound"]
def IsZeroAbove (M N : ModuleCat R) (n : ℕ) : Prop :=
  ∀ p : ℕ, n < p →
    IsZero (((CategoryTheory.Tor (ModuleCat R) p).obj M).obj N)

/-- `Tor_p^R(M, N)` vanishes for all sufficiently large `p`. -/
@[stacks 09PX "eventual Tor vanishing"]
def EventuallyIsZero (M N : ModuleCat R) : Prop :=
  ∃ n : ℕ, IsZeroAbove M N n

/-- Increasing a Tor-vanishing bound preserves the vanishing condition. -/
theorem IsZeroAbove.mono {M N : ModuleCat R} {n m : ℕ}
    (h : IsZeroAbove M N n) (hnm : n ≤ m) :
    IsZeroAbove M N m := sorry

/-- A specified Tor-vanishing bound gives eventual Tor vanishing. -/
theorem IsZeroAbove.eventually {M N : ModuleCat R} {n : ℕ}
    (h : IsZeroAbove M N n) : EventuallyIsZero M N := sorry

end CategoryTheory.ModuleCat.Tor
