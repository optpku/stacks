module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Definition_90_12_3
public import stacks_project.Chap90.Lemma_90_20_3
public import stacks_project.Chap93.Lemma_93_8_2
public import stacks_project.Chap93.Lemma_93_8_7_Localization

/-!
# Smoothness of localization of ring deformation categories

If `k → P` is of finite type and `Spec P ⟶ Spec k` is smooth at all points of
`zeroLocus {g}` for every `g` in a multiplicative subset `S ⊆ P`, then
`localizationBasedFunctor Λ k S` is smooth and induces a bijection on tangent
spaces.
-/

@[expose] public section

open CategoryTheory
open Algebra
open PrimeSpectrum

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {P : Type u} [CommRing P] [Algebra k P]

namespace FlatAlgebraCat

/-- Lemma 93.13.3 (1)
In Example 93.8.1, let `P` be a finite type `k`-algebra and let `S ⊆ P` be a
multiplicative subset such that `Spec P ⟶ Spec k` is smooth at all points of
`zeroLocus {g}` for all `g ∈ S`. Then `localizationBasedFunctor Λ k S` is
smooth. -/
@[stacks 0DZ9]
theorem isSmooth_localizationBasedFunctor [Algebra.FiniteType k P] (S : Submonoid P)
    (hS : ∀ g ∈ S, zeroLocus ({g} : Set P) ⊆ smoothLocus k P) :
    BasedFunctor.IsSmooth (localizationBasedFunctor Λ k S) := sorry

/-- Lemma 93.13.3 (2)
In Example 93.8.1, let `P` be a finite type `k`-algebra and let `S ⊆ P` be a
multiplicative subset such that `Spec P ⟶ Spec k` is smooth at all points of
`zeroLocus {g}` for all `g ∈ S`. Then the differential of
`localizationBasedFunctor Λ k S` is bijective on tangent spaces. -/
@[stacks 0DZ9]
theorem bijective_differential_localizationBasedFunctor [Algebra.FiniteType k P]
    (S : Submonoid P)
    (hS : ∀ g ∈ S, zeroLocus ({g} : Set P) ⊆ smoothLocus k P) :
    Function.Bijective (BasedFunctor.differential (localizationBasedFunctor Λ k S)) :=
  sorry

/-- Smoothness of `Spec P ⟶ Spec k` at every point of `zeroLocus {g}` for `g ∈ S`
is equivalent to `S` meeting no prime outside `smoothLocus k P`. -/
theorem smoothAtZeroLocus_iff_disjoint_nonsmooth (S : Submonoid P) :
    (∀ g ∈ S, zeroLocus ({g} : Set P) ⊆ smoothLocus k P) ↔
      ∀ q : PrimeSpectrum P, q ∉ smoothLocus k P → (S : Set P) ∩ q.asIdeal = ∅ :=
  sorry

end FlatAlgebraCat
