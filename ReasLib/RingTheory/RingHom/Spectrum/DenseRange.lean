/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Dense maps on prime spectra

Mathlib already characterizes density of `PrimeSpectrum.comap f` by the kernel of `f` and by
minimal prime ideals.  This leaf adds the intrinsic minimal-point view, the source-facing TFAE,
and the domain specialization relating density to injectivity and the generic point.

@stack 00FJ
@stack 00FL
-/

universe u v

namespace PrimeSpectrum

section General

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]

/-
API design: the two existing Mathlib criteria remain canonical and are reused directly.  Only
the `IsMin` point-language bridge is new; it is the form consumed by topological and scheme-level
arguments.  A named pairwise theorem accompanies the TFAE so downstream users never need to
index into `List.TFAE` merely to move between the point and density views.
-/

/-- Density of `Spec(S) → Spec(R)` is equivalent to every minimal point of `Spec(R)` lying in
its range. -/
@[stacks 00FL "dense spectrum map and minimal points"]
theorem denseRange_comap_iff_minimalPoints (f : R →+* S) :
    DenseRange (comap f) ↔
      ∀ p : PrimeSpectrum R, IsMin p → p ∈ Set.range (comap f) := sorry

/-- Lemma 10.30.6 (Tag 00FL): the kernel, minimal-point, and dense-range criteria for a map on
prime spectra. -/
@[stacks 00FL "dense-range criteria for prime spectra"]
theorem denseRange_comap_tfae (f : R →+* S) :
    List.TFAE
      [ RingHom.ker f ≤ nilradical R,
        ∀ p : PrimeSpectrum R, IsMin p → p ∈ Set.range (comap f),
        DenseRange (comap f) ] := sorry

end General

section Domain

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R]

/- The domain API is kept separate because its generic point and injectivity formulations are
specializations, not assumptions needed by the semiring-level dense-range owner above. -/

/-- For a map out of a domain, density on prime spectra is equivalent to injectivity. -/
@[stacks 00FJ "injectivity and dense maps on prime spectra"]
theorem denseRange_comap_iff_injective (f : R →+* S) :
    DenseRange (comap f) ↔ Function.Injective f := sorry

/-- For a map out of a domain, density is equivalent to the generic point lying in the range. -/
@[stacks 00FJ "dense spectrum map and the generic point"]
theorem denseRange_comap_iff_genericPoint_mem_range (f : R →+* S) :
    DenseRange (comap f) ↔
      (⊥ : PrimeSpectrum R) ∈ Set.range (comap f) := sorry

/-- Lemma 10.30.4 (Tag 00FJ): injectivity, dense range on spectra, and occurrence of the generic
point are equivalent for a map out of a domain. -/
@[stacks 00FJ "domain map and dense prime-spectrum range"]
theorem denseRange_comap_tfae_of_domain (f : R →+* S) :
    List.TFAE
      [ Function.Injective f,
        DenseRange (comap f),
        (⊥ : PrimeSpectrum R) ∈ Set.range (comap f) ] := sorry

end Domain

end PrimeSpectrum
