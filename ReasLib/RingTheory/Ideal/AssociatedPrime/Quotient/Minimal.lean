module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated primes of quotients without embedded primes

@stack 031T
-/

@[expose] public section

universe u

namespace associatedPrimes.Quotient

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- If `R / I` has no embedded associated primes, each of its associated primes is minimal over
`I`. -/
@[stacks 031T "associated primes of a quotient without embedded primes"]
theorem mem_minimalPrimes_of_noEmbedded
    (I : Ideal R)
    (h : embeddedAssociatedPrimes R (R ⧸ I) = ∅)
    {p : Ideal R} (hp : p ∈ associatedPrimes R (R ⧸ I)) :
    p ∈ I.minimalPrimes := by
  have hp_min : Minimal (· ∈ associatedPrimes R (R ⧸ I)) p :=
    (embeddedAssociatedPrimes_eq_empty_iff (R := R) (M := R ⧸ I)).mp h p hp
  have hAnn : Module.annihilator R (R ⧸ I) = I := Ideal.annihilator_quotient
  have hIle : I ≤ p := by
    rw [← hAnn]
    rw [← Submodule.annihilator_top]
    exact IsAssociatedPrime.annihilator_le (M := R ⧸ I) hp
  refine ⟨⟨hp.1, hIle⟩, ?_⟩
  intro q hq hqp
  letI : q.IsPrime := hq.1
  obtain ⟨r, hr, hrq⟩ := Ideal.exists_minimalPrimes_le hq.2
  have hr_assoc : r ∈ associatedPrimes R (R ⧸ I) := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    rwa [hAnn]
  exact (hp_min.2 hr_assoc (hrq.trans hqp)).trans hrq

end associatedPrimes.Quotient
