/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Dimension

/-!
# Dimension-zero characterizations of Artinian rings

This file records the ten equivalent forms of Proposition 10.60.7.

@stack 00KJ
-/

@[expose] public section

universe u

namespace IsArtinianRing

/-- Proposition 10.60.7 (Tag `00KJ`): the Artinian condition is equivalent to the
standard Noetherian dimension-zero, finite-length, finite-product, discrete-spectrum,
Hilbert-Samuel, nilpotent-Jacobson, and prime-incomparability formulations. -/
@[stacks 00KJ "ten equivalent Artinian-ring criteria"]
theorem dimensionZero_tfae (R : Type u) [CommRing R] :
    List.TFAE
      [ IsArtinianRing R
      , IsNoetherianRing R ∧ Ring.KrullDimLE 0 R
      , IsFiniteLength R R
      , ∃ (ι : Type u) (_ : Fintype ι) (S : ι → Type u)
          (_ : ∀ i, CommRing (S i)) (_ : ∀ i, IsLocalRing (S i))
          (_ : R ≃+* ∀ i, S i),
          ∀ i, IsArtinianRing (S i)
      , IsNoetherianRing R ∧ DiscreteTopology (PrimeSpectrum R)
      , ∃ (ι : Type u) (_ : Fintype ι) (S : ι → Type u)
          (_ : ∀ i, CommRing (S i)) (_ : ∀ i, IsLocalRing (S i))
          (_ : ∀ i, IsNoetherianRing (S i)) (_ : R ≃+* ∀ i, S i),
          ∀ i, Ring.KrullDimLE 0 (S i)
      , ∃ (ι : Type u) (_ : Fintype ι) (S : ι → Type u)
          (_ : ∀ i, CommRing (S i)) (_ : ∀ i, IsLocalRing (S i))
          (_ : ∀ i, IsNoetherianRing (S i)) (_ : R ≃+* ∀ i, S i),
          ∀ i, Ideal.HilbertSamuel.degree (S i) (S i) = 0
      , ∃ (ι : Type u) (_ : Fintype ι) (S : ι → Type u)
          (_ : ∀ i, CommRing (S i)) (_ : ∀ i, IsLocalRing (S i))
          (_ : ∀ i, IsNoetherianRing (S i)) (_ : R ≃+* ∀ i, S i),
          ∀ i, IsNilpotent (IsLocalRing.maximalIdeal (S i))
      , IsNoetherianRing R ∧
          Finite (MaximalSpectrum R) ∧
          IsNilpotent (Ring.jacobson R)
      , IsNoetherianRing R ∧
          ∀ ⦃p q : Ideal R⦄, p.IsPrime → q.IsPrime → p ≤ q → p = q
      ] := sorry

end IsArtinianRing
