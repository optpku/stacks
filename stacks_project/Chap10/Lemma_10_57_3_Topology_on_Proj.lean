/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Lemma 10.57.3 (Topology on Proj)

The standard-open, closed-set, affine-chart, and non-quasi-compactness properties of `Proj`.

@stack 00JP
-/

open AlgebraicGeometry ProjectiveSpectrum

universe u v

section ProjectiveSpectrumTopology

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Lemma 10.57.3 (Topology on Proj) (1): every `D₊(f)` is open. -/
#check @ProjectiveSpectrum.isOpen_basicOpen

/- Lemma 10.57.3 (Topology on Proj) (2): `D₊(f f') = D₊(f) ∩ D₊(f')`. -/
#check @ProjectiveSpectrum.basicOpen_mul

/-- Lemma 10.57.3 (Topology on Proj) (3): the restriction of `D(g)` to `Proj(A)` is the
union of the degree-zero part and the positive-degree homogeneous parts of `g`. -/
@[stacks 00JP]
theorem proj_basicOpen_eq_projZero_sup_iSup_pos (g : A) :
    Proj.basicOpen 𝒜 g =
      Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ⊔
        ⨆ i : {n : ℕ // 1 ≤ n}, Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g) := sorry

/-- Lemma 10.57.3 (Topology on Proj) (4): a degree-zero standard open is covered by
positive-degree standard opens cut out by its homogeneous multiples. -/
@[stacks 00JP]
theorem proj_basicOpen_degreeZero_eq_iSup_mul (g₀ : 𝒜 0) :
    Proj.basicOpen 𝒜 (g₀ : A) =
      ⨆ d : {n : ℕ // 0 < n}, ⨆ f : 𝒜 d.1,
        Proj.basicOpen 𝒜 ((g₀ : A) * (f : A)) := sorry

/- Lemma 10.57.3 (Topology on Proj) (5): the standard opens form a basis. -/
#check @AlgebraicGeometry.Proj.isBasis_basicOpen

/- Lemma 10.57.3 (Topology on Proj) (6): a positive-degree standard open is canonically
isomorphic to the spectrum of the degree-zero homogeneous localization. Together with Lemma
10.57.2, this gives the two homeomorphisms through the homogeneous primes of `A_f`. -/
#check @AlgebraicGeometry.Proj.basicOpenIsoSpec

end ProjectiveSpectrumTopology

namespace MvPolynomial

-- The source's concrete example uses the standard total-degree grading, one of several possible
-- gradings on an infinite-variable polynomial ring.
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Lemma 10.57.3 (Topology on Proj) (7): the projective spectrum of the standard-graded
polynomial ring `ℤ[X₀, X₁, …]` is not quasi-compact. -/
@[stacks 00JP]
theorem projectiveSpectrum_nat_not_isCompactSpace :
    ¬ CompactSpace
      (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule ℕ ℤ)) := sorry

end MvPolynomial

section ProjectiveSpectrumClosedSets

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Lemma 10.57.3 (Topology on Proj) (8): every `V₊(I)` is closed. -/
#check @ProjectiveSpectrum.isClosed_zeroLocus

/-- Lemma 10.57.3 (Topology on Proj) (9): every closed subset is the zero locus of a
homogeneous ideal. -/
@[stacks 00JP]
theorem isClosed_iff_exists_zeroLocus_homogeneousIdeal
    (T : Set (ProjectiveSpectrum 𝒜)) :
    IsClosed T ↔ ∃ I : HomogeneousIdeal 𝒜, T = zeroLocus 𝒜 (I : Set A) := sorry

/-- Lemma 10.57.3 (Topology on Proj) (10): the zero locus of a homogeneous ideal is empty
exactly when its radical contains the irrelevant ideal. -/
@[stacks 00JP]
theorem zeroLocus_eq_empty_iff_irrelevant_le_radical (I : HomogeneousIdeal 𝒜) :
    zeroLocus 𝒜 (I : Set A) = ∅ ↔
      HomogeneousIdeal.irrelevant 𝒜 ≤ I.radical := sorry

end ProjectiveSpectrumClosedSets
