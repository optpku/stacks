/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import ReasLib.LinearAlgebra.TensorProduct.Surjective
public import ReasLib.RingTheory.Module.Support.Fiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local and residue-fiber loci of linear maps

For a map `φ : M →ₗ[R] N`, the intrinsic owner of its local-surjectivity locus
is the complement of the support of the cokernel `N ⧸ φ.range`.  The residue
fiber is exposed through Mathlib's `LinearMap.baseChange` and `Ideal.Fiber`;
the older right-tensor presentation is retained only as a bridge theorem.

@stack 05GE
@stack 05GF
@stack 00O0
-/

@[expose] public section

universe u v w

open PrimeSpectrum

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- `φ` is surjective at `p` when its canonical localization at `p` is surjective. -/
@[stacks 05GE "localized surjectivity at a prime"]
abbrev IsSurjectiveAt (φ : M →ₗ[R] N) (p : PrimeSpectrum R) : Prop :=
  Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ)

/-- The set of primes where a linear map becomes surjective after localization. -/
@[stacks 05GE "localized surjectivity locus"]
def surjectiveLocus (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | φ.IsSurjectiveAt p}

/-- `φ` is fiber-surjective at `p` when its canonical residue-field base change is surjective. -/
@[stacks 05GE "residue-fiber surjectivity at a prime"]
abbrev IsFiberSurjectiveAt (φ : M →ₗ[R] N) (p : PrimeSpectrum R) : Prop :=
  Function.Surjective (φ.baseChange p.asIdeal.ResidueField)

/-- `φ` is injective at `p` when its canonical localization at `p` is injective. -/
@[stacks 05GF "localized injectivity at a prime"]
abbrev IsInjectiveAt (φ : M →ₗ[R] N) (p : PrimeSpectrum R) : Prop :=
  Function.Injective (LocalizedModule.map p.asIdeal.primeCompl φ)

/-- The set of primes where a linear map becomes injective after localization. -/
@[stacks 05GF "localized injectivity locus"]
def injectiveLocus (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | φ.IsInjectiveAt p}

/-- `φ` is bijective at `p` when its canonical localization at `p` is bijective. -/
@[stacks 05GF "localized bijectivity at a prime"]
abbrev IsBijectiveAt (φ : M →ₗ[R] N) (p : PrimeSpectrum R) : Prop :=
  Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl φ)

/-- The set of primes where a linear map becomes bijective after localization. -/
@[stacks 05GF "localized bijectivity locus"]
def bijectiveLocus (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | φ.IsBijectiveAt p}

/-- `φ` is fiber-injective at `p` when its canonical residue-field base change is injective. -/
@[stacks 00O0 "residue-fiber injectivity at a prime"]
abbrev IsFiberInjectiveAt (φ : M →ₗ[R] N) (p : PrimeSpectrum R) : Prop :=
  Function.Injective (φ.baseChange p.asIdeal.ResidueField)

/-- The set of primes where the residue-field fiber map of `φ` is injective. -/
@[stacks 00O0 "residue-fiber injectivity locus"]
def fiberInjectiveLocus (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | φ.IsFiberInjectiveAt p}

/-- `φ` is fiber-bijective at `p` when its canonical residue-field base change is bijective. -/
@[stacks 00O0 "residue-fiber bijectivity at a prime"]
abbrev IsFiberBijectiveAt (φ : M →ₗ[R] N) (p : PrimeSpectrum R) : Prop :=
  Function.Bijective (φ.baseChange p.asIdeal.ResidueField)

/-- The set of primes where the residue-field fiber map of `φ` is bijective. -/
@[stacks 00O0 "residue-fiber bijectivity locus"]
def fiberBijectiveLocus (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | φ.IsFiberBijectiveAt p}

/-- The set of primes where the residue-field fiber map of `φ` is surjective. -/
@[stacks 05GE "residue-fiber surjectivity locus"]
def fiberSurjectiveLocus (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | φ.IsFiberSurjectiveAt p}

/-- Membership in `LinearMap.surjectiveLocus` is the pointwise localization predicate. -/
@[simp]
theorem mem_surjectiveLocus_iff (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    p ∈ φ.surjectiveLocus ↔ φ.IsSurjectiveAt p := sorry

/-- Membership in `LinearMap.fiberSurjectiveLocus` is the pointwise fiber predicate. -/
@[simp]
theorem mem_fiberSurjectiveLocus_iff (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    p ∈ φ.fiberSurjectiveLocus ↔ φ.IsFiberSurjectiveAt p := sorry

/-- Membership in `LinearMap.injectiveLocus` is the pointwise localization predicate. -/
@[simp]
theorem mem_injectiveLocus_iff (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    p ∈ φ.injectiveLocus ↔ φ.IsInjectiveAt p := sorry

/-- Membership in `LinearMap.bijectiveLocus` is the pointwise localization predicate. -/
@[simp]
theorem mem_bijectiveLocus_iff (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    p ∈ φ.bijectiveLocus ↔ φ.IsBijectiveAt p := sorry

/-- Membership in `LinearMap.fiberInjectiveLocus` is the pointwise fiber predicate. -/
@[simp]
theorem mem_fiberInjectiveLocus_iff (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    p ∈ φ.fiberInjectiveLocus ↔ φ.IsFiberInjectiveAt p := sorry

/-- Membership in `LinearMap.fiberBijectiveLocus` is the pointwise fiber predicate. -/
@[simp]
theorem mem_fiberBijectiveLocus_iff (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    p ∈ φ.fiberBijectiveLocus ↔ φ.IsFiberBijectiveAt p := sorry

/-- Localized surjectivity is equivalent to lying outside the support of the cokernel. -/
@[stacks 05GE "localized surjectivity detected by cokernel support"]
theorem localized_surjective_iff_notMem_support_coker
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    φ.IsSurjectiveAt p ↔ p ∉ Module.support R (N ⧸ φ.range) := sorry

/-- Fiber surjectivity is equivalent to lying outside the support of a finite cokernel. -/
@[stacks 05GE "residue-fiber surjectivity detected by cokernel support"]
theorem fiber_surjective_iff_notMem_support_coker
    (φ : M →ₗ[R] N) [Module.Finite R (N ⧸ φ.range)] (p : PrimeSpectrum R) :
    φ.IsFiberSurjectiveAt p ↔ p ∉ Module.support R (N ⧸ φ.range) := sorry

/-- The right-tensor presentation of the residue fiber is equivalent to the canonical
`LinearMap.baseChange` presentation. -/
theorem rTensor_surjective_iff_mem_fiberSurjectiveLocus
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Function.Surjective (φ.rTensor p.asIdeal.ResidueField) ↔
      p ∈ φ.fiberSurjectiveLocus := sorry

/-- The localized surjectivity locus is the complement of the cokernel support. -/
@[stacks 05GE "surjectivity locus as a support complement"]
theorem surjectiveLocus_eq_compl_support_coker (φ : M →ₗ[R] N) :
    φ.surjectiveLocus = (Module.support R (N ⧸ φ.range))ᶜ := sorry

/-- For a finite cokernel, the residue-fiber surjectivity locus has the same support description. -/
@[stacks 05GE "fiber surjectivity locus as a support complement"]
theorem fiberSurjectiveLocus_eq_compl_support_coker
    (φ : M →ₗ[R] N) [Module.Finite R (N ⧸ φ.range)] :
    φ.fiberSurjectiveLocus = (Module.support R (N ⧸ φ.range))ᶜ := sorry

/-- For a finite cokernel, localized and residue-fiber surjectivity define the same locus. -/
@[stacks 05GE "localized and residue-fiber surjectivity loci"]
theorem surjectiveLocus_eq_fiberSurjectiveLocus
    (φ : M →ₗ[R] N) [Module.Finite R (N ⧸ φ.range)] :
    φ.surjectiveLocus = φ.fiberSurjectiveLocus := sorry

/-- Lemma 10.79.1 (1): for a finite target module, localized and
residue-fiber surjectivity define the same locus. -/
@[stacks 05GE "(1), finite-target specialization"]
theorem surjectiveLocus_eq_fiberSurjectiveLocus_of_finite
    (φ : M →ₗ[R] N) [Module.Finite R N] :
    φ.surjectiveLocus = φ.fiberSurjectiveLocus := sorry

/-- The localized surjectivity locus is open when the cokernel is finite. -/
@[stacks 05GE "openness of the surjectivity locus"]
theorem isOpen_surjectiveLocus
    (φ : M →ₗ[R] N) [Module.Finite R (N ⧸ φ.range)] :
    IsOpen φ.surjectiveLocus := sorry

/-- Lemma 10.79.1 (2): the localized surjectivity locus of a map with
finite target is open. -/
@[stacks 05GE "(2), finite-target specialization"]
theorem isOpen_surjectiveLocus_of_finite
    (φ : M →ₗ[R] N) [Module.Finite R N] :
    IsOpen φ.surjectiveLocus := sorry

/-- A basic open lies in the surjectivity locus exactly when the corresponding away-localized map
is surjective.  No finiteness hypothesis is needed for this local-to-away criterion. -/
@[stacks 05GE "basic-open criterion for localized surjectivity"]
theorem basicOpen_subset_surjectiveLocus_iff
    (φ : M →ₗ[R] N) (f : R) :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ φ.surjectiveLocus ↔
      Function.Surjective (LocalizedModule.map (.powers f) φ) := sorry

/-- Lemma 10.79.1 (3): if a basic open lies in the localized
surjectivity locus, then the corresponding away-localized map is surjective. -/
@[stacks 05GE "(3), forward direction"]
theorem surjective_away_of_basicOpen_subset_surjectiveLocus
    (φ : M →ₗ[R] N) (f : R)
    (h : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ φ.surjectiveLocus) :
    Function.Surjective (LocalizedModule.map (.powers f) φ) := sorry

/-- Localized injectivity is equivalent to lying outside the support of the kernel. -/
@[stacks 05GF "localized injectivity detected by kernel support"]
theorem injectiveAt_iff_notMem_support_ker (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    φ.IsInjectiveAt p ↔ p ∉ Module.support R φ.ker := sorry

/-- Localized bijectivity is equivalent to lying outside the supports of the kernel and cokernel. -/
@[stacks 05GF "localized bijectivity detected by kernel and cokernel support"]
theorem bijectiveAt_iff_notMem_support_ker_and_coker
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    φ.IsBijectiveAt p ↔
      p ∉ Module.support R φ.ker ∧ p ∉ Module.support R (N ⧸ φ.range) := sorry

/-- The localized bijectivity locus is the intersection of the complements of kernel and
cokernel support. -/
@[stacks 05GF "localized bijectivity locus as support complements"]
theorem bijectiveLocus_eq_compl_support_ker_inter_compl_support_coker
    (φ : M →ₗ[R] N) :
    φ.bijectiveLocus =
      (Module.support R φ.ker)ᶜ ∩ (Module.support R (N ⧸ φ.range))ᶜ := sorry

/-- Injectivity after localization at a submonoid is equivalent to vanishing of the localized
kernel. -/
@[stacks 05GF "localized injectivity and kernel vanishing"]
theorem localized_injective_iff_subsingleton_ker
    (φ : M →ₗ[R] N) (S : Submonoid R) :
    Function.Injective (LocalizedModule.map S φ) ↔
      Subsingleton (LocalizedModule S φ.ker) := sorry

/-- A bijection after localizing away from `f` remains a bijection at every prime of `D(f)`. -/
@[stacks 05GF "away-localized bijectivity on a basic open"]
theorem basicOpen_subset_bijectiveLocus_of_bijective_away
    (φ : M →ₗ[R] N) {f : R}
    (hbij : Function.Bijective (LocalizedModule.map (.powers f) φ)) :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ φ.bijectiveLocus := sorry

/-- Lemma 10.79.2: the local bijectivity locus of a map from a finite module to a finitely
presented module is open. -/
@[stacks 05GF]
theorem isOpen_bijectiveLocus
    (φ : M →ₗ[R] N) [Module.Finite R M] [Module.FinitePresentation R N] :
    IsOpen φ.bijectiveLocus := sorry

/-- The right-tensor presentation of a residue fiber is injective exactly on the canonical
fiber-injectivity locus. -/
@[stacks 00O0 "right-tensor view of fiber injectivity"]
theorem rTensor_injective_iff_mem_fiberInjectiveLocus
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Function.Injective (φ.rTensor p.asIdeal.ResidueField) ↔
      p ∈ φ.fiberInjectiveLocus := sorry

/-- The right-tensor presentation of a residue fiber is bijective exactly on the canonical
fiber-bijectivity locus. -/
@[stacks 00O0 "right-tensor view of fiber bijectivity"]
theorem rTensor_bijective_iff_mem_fiberBijectiveLocus
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Function.Bijective (φ.rTensor p.asIdeal.ResidueField) ↔
      p ∈ φ.fiberBijectiveLocus := sorry

section FiniteProjective

variable [Module.Finite R M] [Module.Projective R M]
variable [Module.Finite R N] [Module.Projective R N]

/-- Lemma 10.79.4 (1): the residue-fiber injectivity locus of a map between finite projective
modules is open. -/
@[stacks 00O0 "(1), open fiber-injectivity locus"]
theorem isOpen_fiberInjectiveLocus (φ : M →ₗ[R] N) :
    IsOpen φ.fiberInjectiveLocus := sorry

/-- Lemma 10.79.4 (2): a map is injective after localizing away from a basic open contained in
its residue-fiber injectivity locus. -/
@[stacks 00O0 "(2), away-localized injectivity"]
theorem injective_away_of_basicOpen_subset_fiberInjectiveLocus
    (φ : M →ₗ[R] N) (f : R)
    (h : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ φ.fiberInjectiveLocus) :
    Function.Injective (LocalizedModule.map (.powers f) φ) := sorry

/-- Lemma 10.79.4 (3): on the same basic open, the localized cokernel is finite projective. -/
@[stacks 00O0 "(3), finite projective away-localized cokernel"]
theorem coker_away_finite_projective_of_basicOpen_subset_fiberInjectiveLocus
    (φ : M →ₗ[R] N) (f : R)
    (h : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ φ.fiberInjectiveLocus) :
    Module.Finite (Localization.Away f) (LocalizedModule.Away f (N ⧸ φ.range)) ∧
      Module.Projective (Localization.Away f) (LocalizedModule.Away f (N ⧸ φ.range)) := sorry

/-- Lemma 10.79.4 (4): the residue-fiber surjectivity locus of a map between finite projective
modules is open. -/
@[stacks 00O0 "(4), open fiber-surjectivity locus"]
theorem isOpen_fiberSurjectiveLocus (φ : M →ₗ[R] N) :
    IsOpen φ.fiberSurjectiveLocus := sorry

/-- Lemma 10.79.4 (5): a map is surjective after localizing away from a basic open contained in
its residue-fiber surjectivity locus. -/
@[stacks 00O0 "(5), away-localized surjectivity"]
theorem surjective_away_of_basicOpen_subset_fiberSurjectiveLocus
    (φ : M →ₗ[R] N) (f : R)
    (h : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ φ.fiberSurjectiveLocus) :
    Function.Surjective (LocalizedModule.map (.powers f) φ) := sorry

/-- Lemma 10.79.4 (6): on the same basic open, the localized kernel is finite projective. -/
@[stacks 00O0 "(6), finite projective away-localized kernel"]
theorem ker_away_finite_projective_of_basicOpen_subset_fiberSurjectiveLocus
    (φ : M →ₗ[R] N) (f : R)
    (h : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ φ.fiberSurjectiveLocus) :
    Module.Finite (Localization.Away f) (LocalizedModule.Away f φ.ker) ∧
      Module.Projective (Localization.Away f) (LocalizedModule.Away f φ.ker) := sorry

/-- Lemma 10.79.4 (7): the residue-fiber bijectivity locus of a map between finite projective
modules is open. -/
@[stacks 00O0 "(7), open fiber-bijectivity locus"]
theorem isOpen_fiberBijectiveLocus (φ : M →ₗ[R] N) :
    IsOpen φ.fiberBijectiveLocus := sorry

/-- Lemma 10.79.4 (8): a map is bijective after localizing away from a basic open contained in
its residue-fiber bijectivity locus. -/
@[stacks 00O0 "(8), away-localized bijectivity"]
theorem bijective_away_of_basicOpen_subset_fiberBijectiveLocus
    (φ : M →ₗ[R] N) (f : R)
    (h : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ φ.fiberBijectiveLocus) :
    Function.Bijective (LocalizedModule.map (.powers f) φ) := sorry

end FiniteProjective

end LinearMap
