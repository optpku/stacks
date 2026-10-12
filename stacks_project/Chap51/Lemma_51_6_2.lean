/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Sequential
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Set TopologicalSpace

universe u

open CategoryTheory.ModuleCat.SupportedOn

/- Lemma 51.6.2: for a finite-dimensional Noetherian ring, a specialization-stable
subset `T` of the prime spectrum, and a sequential inverse system `F` of modules,
eventual vanishing of every localized point-term transition implies eventual
vanishing of the transition on supported local cohomology after `2 ^ dim(T)`
iterations of the stabilization function, with the empty-support dimension
normalized to zero. -/
@[stacks 0EF9] #check (CategoryTheory.ModuleCat.SupportedOn.eventuallyZeroSupportedCohomology :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [FiniteRingKrullDim A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (F : SequentialInverseSystem (ModuleCat.{u} A)) (i : ℤ) (hi : 0 ≤ i)
    (m' : ℕ → ℕ) (hm'_ge : ∀ m, m ≤ m' m)
    (h_local : ∀ (m k : ℕ) (h_m'k : m' m ≤ k),
      ∀ (p : PrimeSpectrum A) (hp : p ∈ T),
        localCohomologyTransitionMap F i (Nat.le_trans (hm'_ge m) h_m'k) p = 0),
    ∀ (m k : ℕ) (hmk : m ≤ k),
      (m'^[2 ^ ((topologicalKrullDim T).unbotD 0).toNat]) m ≤ k →
        (supportedCohomologyTower T F i).transitionMap hmk = 0)
