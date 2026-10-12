/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.Ideal.Localization
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

open scoped ENat

universe u v

namespace Module.LocalCohomology

/-- The depth-dimension value associated to two comparable primes of a finite module. -/
noncomputable def pairValue {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p q : PrimeSpectrum A) : WithBot ℕ∞ :=
  .some (moduleDepth (Localization.AtPrime p.asIdeal)
    (LocalizedModule.AtPrime p.asIdeal M)) +
      ringKrullDim (p.asIdeal.quotientAtPrime q)

/-- The admissible depth-dimension values for a finite module along prime chains
from outside `V(I)` to inside `V(I)`. -/
noncomputable def values {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Set (WithBot ℕ∞) :=
  {d | ∃ p q : PrimeSpectrum A,
    ¬ I ≤ p.asIdeal ∧ I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal ∧
      d = pairValue M p q}

/-- The local-cohomology cutoff is the infimum of the admissible values. The
infimum of an empty set is top, and nonempty admissible sets have a minimum. -/
noncomputable def cutoff {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    WithBot ℕ∞ :=
  sInf (values I M)

/-- For comparable primes, the depth-dimension value is not bottom; in
particular, the infinite-depth convention for a zero localization is retained. -/
theorem pairValue_ne_bot {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal) :
    pairValue M p q ≠ ⊥ := sorry

/-- Membership in `values I M` is the existence of an admissible chain of primes
realizing the given depth-dimension value. -/
theorem mem_values {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (d : WithBot ℕ∞) :
    d ∈ values I M ↔ ∃ p q : PrimeSpectrum A,
      ¬ I ≤ p.asIdeal ∧ I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal ∧
        d = pairValue M p q := sorry

/-- The cutoff is at most the depth-dimension value of every admissible pair of primes. -/
theorem cutoff_le_pairValue {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p q : PrimeSpectrum A) (hp : ¬ I ≤ p.asIdeal) (hq : I ≤ q.asIdeal)
    (hpq : p.asIdeal ≤ q.asIdeal) :
    cutoff I M ≤ pairValue M p q := sorry

/-- A value bounds the cutoff from below exactly when it bounds every admissible
depth-dimension value from below. -/
theorem le_cutoff_iff {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (d : WithBot ℕ∞) :
    d ≤ cutoff I M ↔ ∀ p q : PrimeSpectrum A,
      ¬ I ≤ p.asIdeal → I ≤ q.asIdeal → p.asIdeal ≤ q.asIdeal →
        d ≤ pairValue M p q := sorry

/-- A nonempty admissible-value set contains its cutoff, so the infimum is the
minimum of the admissible values. -/
theorem cutoff_mem_values {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hvalues : (values I M).Nonempty) :
    cutoff I M ∈ values I M := sorry

/-- The local-cohomology cutoff is never bottom. -/
theorem cutoff_ne_bot {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    cutoff I M ≠ ⊥ := sorry

end Module.LocalCohomology
