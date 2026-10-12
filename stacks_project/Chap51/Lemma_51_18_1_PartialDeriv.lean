/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPowerSeries.Derivation

@[expose] public section

universe u v

#check (MvPowerSeries.partialDeriv :
  {k : Type u} → [CommSemiring k] → {σ : Type v} →
    σ → Derivation k (MvPowerSeries σ k) (MvPowerSeries σ k))

#check (MvPowerSeries.coeff_partialDeriv :
  ∀ {k : Type u} [CommSemiring k] {σ : Type v}
    (i : σ) (f : MvPowerSeries σ k) (n : σ →₀ ℕ),
    MvPowerSeries.coeff n (MvPowerSeries.partialDeriv i f) =
      (n i + 1) • MvPowerSeries.coeff (n + Finsupp.single i 1) f)
