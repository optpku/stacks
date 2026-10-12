/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Definition_90_12_3
public import stacks_project.Chap93.Lemma_93_14_3_BasedFunctor

/-!
# Smoothness of henselization of ring deformation categories

If `k → P` is of finite type and `Spec P ⟶ Spec k` is smooth on the complement
of `V(J)`, then `henselizationBasedFunctor Λ k P J` is smooth and induces a
bijection on tangent spaces.
-/

@[expose] public section

open CategoryTheory
open Algebra
open PrimeSpectrum
open RingPairCat
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {P : Type u} [CommRing P] [Algebra k P]
variable [henselianPairInclusion.IsRightAdjoint]

namespace FlatAlgebraCat

/-- Lemma 93.14.3 (1)
In Example 93.8.1, let `P` be a finite type `k`-algebra and let `J ⊂ P` be an
ideal such that `Spec P ⟶ Spec k` is smooth on the complement of `V(J)`. Then
the functor `Def_P ⟶ Def_{P^h}` of Lemma 93.8.8 is smooth. -/
@[stacks 0DZD]
theorem isSmooth_henselizationBasedFunctor [Algebra.FiniteType k P] (J : Ideal P)
    (hsmooth : (zeroLocus (J : Set P))ᶜ ⊆ smoothLocus k P) :
    BasedFunctor.IsSmooth (henselizationBasedFunctor Λ k P J) := sorry

/-- Lemma 93.14.3 (2)
In Example 93.8.1, let `P` be a finite type `k`-algebra and let `J ⊂ P` be an
ideal such that `Spec P ⟶ Spec k` is smooth on the complement of `V(J)`. Then
the differential of `henselizationBasedFunctor Λ k P J` is bijective on tangent
spaces. -/
@[stacks 0DZD]
theorem bijective_differential_henselizationBasedFunctor [Algebra.FiniteType k P]
    (J : Ideal P) (hsmooth : (zeroLocus (J : Set P))ᶜ ⊆ smoothLocus k P) :
    Function.Bijective (BasedFunctor.differential (henselizationBasedFunctor Λ k P J)) :=
  sorry

end FlatAlgebraCat
