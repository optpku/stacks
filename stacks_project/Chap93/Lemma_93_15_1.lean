/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Definition_90_12_3
public import stacks_project.Chap93.Lemma_93_8_5
public import stacks_project.Chap93.Lemma_93_15_1_Product
public import stacks_project.Chap93.Lemma_93_15_1_Comparison

/-!
# Isolated singularities of ring deformation categories

If `k → P` is of finite type and `Spec P ⟶ Spec k` is smooth except at finitely
many maximal ideals `m i`, then the maps
`Def_P ⟶ ∏ Def_{P_{m i}} ⟶ ∏ Def_{P_{m i}^h} ⟶ ∏ Def_{P_{m i}^∧}`
are smooth and induce isomorphisms on finite-dimensional tangent spaces.
-/

@[expose] public section

open CategoryTheory Algebra PrimeSpectrum RingPairCat RingHom.SquareZeroExtension
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {P : Type u} [CommRing P] [Algebra k P]
variable {ι : Type u} [Finite ι]

namespace FlatAlgebraCat

/-- Lemma 93.15.1 (1)
In Example 93.8.1 let `P` be a `k`-algebra. Assume that `k → P` is of finite type
and that `Spec P ⟶ Spec k` is smooth except at the maximal ideals `m i` of `P`.
Then the tangent space of `Def_P`, identified with `extOneNaiveCotangent k P P`
as in Lemma 93.8.5, is finite-dimensional. -/
@[stacks 0DZF]
theorem finiteDimensional_extOne_of_isolatedSingularities [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    FiniteDimensional k (extOneNaiveCotangent k P P) :=
  sorry

/-- Lemma 93.15.1 (2)
In Example 93.8.1 let `P` be a finite type `k`-algebra, and assume that
`Spec P ⟶ Spec k` is smooth except at the maximal ideals `m i`. Then the map
of deformation categories `Def_P ⟶ ∏ Def_{P_{m i}}` is smooth. -/
@[stacks 0DZF]
theorem isSmooth_localizationPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    BasedFunctor.IsSmooth (localizationPiBasedFunctor Λ k m) :=
  sorry

/-- Lemma 93.15.1 (3)
In Example 93.8.1 let `P` be a finite type `k`-algebra, and assume that
`Spec P ⟶ Spec k` is smooth except at the maximal ideals `m i`. Then the map
`Def_P ⟶ ∏ Def_{P_{m i}}` induces an isomorphism on tangent spaces. -/
@[stacks 0DZF]
theorem bijective_differential_localizationPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    Function.Bijective (BasedFunctor.differential (localizationPiBasedFunctor Λ k m)) :=
  sorry

variable [henselianPairInclusion.IsRightAdjoint]

/-- Lemma 93.15.1 (4)
In Example 93.8.1 let `P` be a finite type `k`-algebra, and assume that
`Spec P ⟶ Spec k` is smooth except at the maximal ideals `m i`. Then the map
of deformation categories `∏ Def_{P_{m i}} ⟶ ∏ Def_{P_{m i}^h}` is smooth. -/
@[stacks 0DZF]
theorem isSmooth_henselizationPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    BasedFunctor.IsSmooth (henselizationPiBasedFunctor Λ k m) :=
  sorry

/-- Lemma 93.15.1 (5)
In Example 93.8.1 let `P` be a finite type `k`-algebra, and assume that
`Spec P ⟶ Spec k` is smooth except at the maximal ideals `m i`. Then the map
`∏ Def_{P_{m i}} ⟶ ∏ Def_{P_{m i}^h}` induces an isomorphism on tangent spaces. -/
@[stacks 0DZF]
theorem bijective_differential_henselizationPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    Function.Bijective (BasedFunctor.differential (henselizationPiBasedFunctor Λ k m)) :=
  sorry

/-- Lemma 93.15.1 (6)
In Example 93.8.1 let `P` be a finite type `k`-algebra, and assume that
`Spec P ⟶ Spec k` is smooth except at the maximal ideals `m i`. Then the map
of deformation categories `∏ Def_{P_{m i}^h} ⟶ ∏ Def_{P_{m i}^∧}` is smooth. -/
@[stacks 0DZF]
theorem isSmooth_completionPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    BasedFunctor.IsSmooth (completionPiBasedFunctor Λ k m) :=
  sorry

/-- Lemma 93.15.1 (7)
In Example 93.8.1 let `P` be a finite type `k`-algebra, and assume that
`Spec P ⟶ Spec k` is smooth except at the maximal ideals `m i`. Then the map
`∏ Def_{P_{m i}^h} ⟶ ∏ Def_{P_{m i}^∧}` induces an isomorphism on tangent spaces. -/
@[stacks 0DZF]
theorem bijective_differential_completionPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    Function.Bijective (BasedFunctor.differential (completionPiBasedFunctor Λ k m)) :=
  sorry

end FlatAlgebraCat
