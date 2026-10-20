module

public import Mathlib.RingTheory.RingHom.Bijective
public import Mathlib.RingTheory.RingHom.Surjective
public import Mathlib.RingTheory.ZariskisMainTheorem
public import ReasLib.RingTheory.QuasiFinite.FiniteType
import StacksCheckRecall

/-!
# The algebraic Zariski main theorem

@stack 00QB

The pointwise finite-localization construction is owned by the algebraic
Zariski main theorem and the localization charts in the imported library.
This file keeps the three source-facing conclusions for the integral closure.
-/

@[expose] public section

universe u v

open Topology

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S] [Algebra.QuasiFinite R S]

/-! Canonical owners for the three source views. -/

#check @Algebra.ZariskisMainProperty
#check @Algebra.ZariskisMainProperty.of_finiteType
#check @Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective
#check @Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective
#check @PrimeSpectrum.localization_away_isOpenEmbedding

/-- Lemma 10.123.14 (00QB), part (1): the spectrum map from `S` to the
integral closure of `R` in `S` is an open embedding. -/
@[stacks 00QB]
theorem primeSpectrum_comap_integralClosure_isOpenEmbedding :
    IsOpenEmbedding (PrimeSpectrum.comap (integralClosure R S).val.toRingHom) := sorry

/-- Lemma 10.123.14 (00QB), part (2): a basic open of the integral closure
contained in the image has bijective localization map to `S`. -/
@[stacks 00QB]
theorem awayMap_bijective_of_basicOpen_subset_range_integralClosure
    (g : integralClosure R S)
    (hg :
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (integralClosure R S))) ⊆
        Set.range (PrimeSpectrum.comap (integralClosure R S).val.toRingHom))) :
    Function.Bijective (Localization.awayMap (integralClosure R S).val.toRingHom g) := sorry

/-- Lemma 10.123.14 (00QB), part (3): a finite `R`-subalgebra of the
integral closure carries the same open-embedding and principal-localization
properties. -/
@[stacks 00QB]
theorem exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties :
    ∃ S'' : Subalgebra R S,
      S'' ≤ integralClosure R S ∧
      Module.Finite R S'' ∧
      IsOpenEmbedding (PrimeSpectrum.comap S''.val.toRingHom) ∧
      ∀ g : S'',
        ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S'')) ⊆
          Set.range (PrimeSpectrum.comap S''.val.toRingHom)) →
          Function.Bijective (Localization.awayMap S''.val.toRingHom g) := sorry

end

end
