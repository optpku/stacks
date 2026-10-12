/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.AtPrime
public import ReasLib.RingTheory.Support.Cyclic
import StacksCheckRecall

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Exercise 111.7.2: the image of `m` in the localization at `p` is nonzero iff
`Ideal.torsionOf R M m ≤ p.asIdeal`. Equivalently, in the source polarity,
`LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m = 0` iff
`¬ (Ideal.torsionOf R M m ≤ p.asIdeal)`, by classical negation. -/
@[stacks 0768]
#check (LocalizedModule.mkLinearMap_apply_ne_zero_iff_torsionOf_le :
  ∀ (p : PrimeSpectrum R) (m : M),
    LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m ≠ 0 ↔
      Ideal.torsionOf R M m ≤ p.asIdeal)

/- Companion: the annihilator `{a : R | a • m = 0}` is the ideal
`Ideal.torsionOf R M m`. -/
#check (Ideal.torsionOf R M : M → Ideal R)

/- Companion: membership in the annihilator is exactly scalar annihilation. -/
#check (Ideal.mem_torsionOf_iff :
  ∀ (m : M) (a : R), a ∈ Ideal.torsionOf R M m ↔ a • m = 0)

/- Companion: an element is zero iff its image is zero at every prime ideal. -/
#check (LocalizedModule.AtPrime.eq_zero_iff_forall_prime :
  ∀ (m : M), m = 0 ↔ ∀ (P : Ideal R) [P.IsPrime],
    LocalizedModule.mkLinearMap P.primeCompl M m = 0)

/- Companion: an element is zero iff its image is zero at every maximal ideal. -/
#check (LocalizedModule.AtPrime.eq_zero_iff_forall_maximal :
  ∀ (m : M), m = 0 ↔ ∀ (P : Ideal R) [P.IsMaximal],
    LocalizedModule.mkLinearMap P.primeCompl M m = 0)

/- Companion: vanishing of an element is equivalent after localizing at all primes
or only at all maximal ideals. -/
#check (LocalizedModule.AtPrime.eq_zero_tfae :
  ∀ (m : M), List.TFAE [
    m = 0,
    ∀ (P : Ideal R) [P.IsPrime], LocalizedModule.mkLinearMap P.primeCompl M m = 0,
    ∀ (P : Ideal R) [P.IsMaximal], LocalizedModule.mkLinearMap P.primeCompl M m = 0
  ])

/- Companion: `M = 0` (as `Subsingleton M`) iff
`Subsingleton (LocalizedModule.AtPrime P M)` for every maximal ideal `P`. -/
#check (LocalizedModule.AtPrime.subsingleton_iff_forall_maximal :
  Subsingleton M ↔ ∀ (P : Ideal R) [P.IsMaximal],
    Subsingleton (LocalizedModule.AtPrime P M))
