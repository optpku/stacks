/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ComplementaryPowers
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 42.3.3: if `φ ^ n = 0` for `0 < n` and
`ker φ / range (φ ^ (n - 1))` has finite length, then the multiplicity of the
two-periodic complex with differentials `φ ^ i` and `φ ^ (n - i)` is zero for every
`i ≤ n`. -/
@[stacks 0EAB] #check
  (CategoryTheory.TwoPeriodicEndomorphism.eulerMultiplicity_ofPowers_eq_zero :
    ∀ {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
      (φ : Module.End R M) (n : ℕ) (hn : 0 < n) (hnil : φ ^ n = 0)
      (hfinite : IsFiniteLength R (φ.ker ⧸ (φ ^ (n - 1)).range.submoduleOf φ.ker))
      (i : ℕ) (hi : i ≤ n),
      (CategoryTheory.TwoPeriodicEndomorphism.ofPowers φ n i hi hnil).multiplicity
        (CategoryTheory.TwoPeriodicEndomorphism.ofPowers_homology_zero_isFiniteLength
          φ n hn hnil hfinite i hi)
        (CategoryTheory.TwoPeriodicEndomorphism.ofPowers_homology_one_isFiniteLength
          φ n hn hnil hfinite i hi) = 0)
