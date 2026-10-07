module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Support
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Support of Cyclic Modules
-/

@[expose] public section

universe u v

namespace LocalizedModule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- An element remains nonzero after localizing at a prime exactly when its torsion ideal is
contained in that prime. -/
@[stacks 07Z5 "localized element and torsion ideal"]
theorem mkLinearMap_apply_ne_zero_iff_torsionOf_le
    (p : PrimeSpectrum R) (m : M) :
    mkLinearMap p.asIdeal.primeCompl M m ≠ 0 ↔
      Ideal.torsionOf R M m ≤ p.asIdeal := by
  constructor
  · intro h r hr
    by_contra hrp
    apply h
    rw [← LinearMap.mem_ker]
    exact mem_ker_mkLinearMap_iff.mpr
      ⟨r, hrp, (Ideal.mem_torsionOf_iff m r).mp hr⟩
  · intro h hzero
    have hmker : m ∈ LinearMap.ker (mkLinearMap p.asIdeal.primeCompl M) :=
      LinearMap.mem_ker.mpr hzero
    obtain ⟨r, hrp, hrm⟩ := mem_ker_mkLinearMap_iff.mp hmker
    exact hrp (h ((Ideal.mem_torsionOf_iff m r).mpr hrm))

end LocalizedModule

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A prime belongs to the support of a cyclic module exactly when its generator remains nonzero
after localization at that prime. -/
@[stacks 07Z5 "cyclic support and localized generator"]
theorem mem_support_span_singleton_iff_mkLinearMap_ne_zero
    (p : PrimeSpectrum R) (m : M) :
    p ∈ Module.support R (R ∙ m) ↔
      LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m ≠ 0 := by
  have hann : Module.annihilator R (R ∙ m) = (R ∙ m).annihilator := by
    ext r
    simp only [Module.mem_annihilator]
  rw [Module.support_eq_zeroLocus, hann,
    Ideal.annihilator_span_singleton_eq_torsionOf,
    PrimeSpectrum.mem_zeroLocus]
  change Ideal.torsionOf R M m ≤ p.asIdeal ↔ _
  exact (LocalizedModule.mkLinearMap_apply_ne_zero_iff_torsionOf_le p m).symm

end Module

namespace PrimeSpectrum

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The zero locus of an element's torsion ideal records precisely the primes where that element
remains nonzero after localization. -/
@[stacks 07Z5 "torsion zero locus and localized element"]
theorem mem_zeroLocus_torsionOf_iff_mkLinearMap_ne_zero
    (p : PrimeSpectrum R) (m : M) :
    p ∈ zeroLocus (Ideal.torsionOf R M m) ↔
      LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m ≠ 0 := by
  rw [PrimeSpectrum.mem_zeroLocus]
  change Ideal.torsionOf R M m ≤ p.asIdeal ↔ _
  exact (LocalizedModule.mkLinearMap_apply_ne_zero_iff_torsionOf_le p m).symm

end PrimeSpectrum
