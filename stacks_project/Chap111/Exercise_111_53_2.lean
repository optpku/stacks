/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.PrimeAvoidance
public import ReasLib.RingTheory.Spectrum.Prime.PairOpen
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.PairOpen
import StacksCheckRecall

@[expose] public section

universe u v

/- Exercise 111.53.2 (1): two-prime avoidance for an ideal. -/
@[stacks 069S]
#check (Ideal.not_subset_union :
  ∀ {A : Type u} [CommRing A] (I q1 q2 : Ideal A) [q1.IsPrime] [q2.IsPrime],
    (¬ I ≤ q1) → (¬ I ≤ q2) →
      ¬ ((I : Set A) ⊆ (q1 : Set A) ∪ (q2 : Set A)))

/- Exercise 111.53.2 (2): two points outside an affine zero locus lie in a common basic open. -/
@[stacks 069S]
#check (PrimeSpectrum.exists_basicOpen_pair :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (x1 x2 : PrimeSpectrum A),
    (x1 ∉ PrimeSpectrum.zeroLocus (I : Set A)) →
      (x2 ∉ PrimeSpectrum.zeroLocus (I : Set A)) →
        ∃ f ∈ I, x1 ∈ PrimeSpectrum.basicOpen f ∧ x2 ∈ PrimeSpectrum.basicOpen f)

/- Exercise 111.53.2 (3): two projective-spectrum points lie in a common standard open. -/
@[stacks 069S]
#check (AlgebraicGeometry.Proj.exists_basicOpen_pair :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (x1 x2 : AlgebraicGeometry.Proj 𝒜),
    ∃ (d : ℕ) (F : A), 0 < d ∧ F ∈ 𝒜 d ∧
      x1 ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 F ∧
      x2 ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 F)
