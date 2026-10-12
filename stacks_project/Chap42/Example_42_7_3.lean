/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.DimensionOne
import ReasLib.RingTheory.Catenary.DimensionFunction.DimensionOne
import stacks_project.Chap29.Lemma_29_17_5
import stacks_project.Chap42.Situation_42_7_1

open AlgebraicGeometry

universe u

/- Example 42.7.3 (1): the spectrum of a one-dimensional Noetherian domain is universally
catenary. -/
@[stacks 02QN] #check
  (AlgebraicGeometry.UniversallyCatenary.specOfDimOneDomain :
    ∀ {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A],
      ringKrullDim A = 1 →
        AlgebraicGeometry.UniversallyCatenary (Spec (CommRingCat.of A)))

/- Example 42.7.3 (2): on a one-dimensional domain, the quotient Krull dimension is zero
exactly at maximal points. -/
@[stacks 02QN] #check
  (PrimeSpectrum.quotientKrullDim.eq_zero_iff_isMaximal :
    ∀ {A : Type u} [CommRing A] [IsDomain A], ringKrullDim A = 1 →
      ∀ p : PrimeSpectrum A,
        PrimeSpectrum.quotientKrullDim p = 0 ↔ p.asIdeal.IsMaximal)

/- Example 42.7.3 (3): on a one-dimensional domain, the quotient Krull dimension is one
exactly at the generic point. -/
@[stacks 02QN] #check
  (PrimeSpectrum.quotientKrullDim.eq_one_iff_eq_bot :
    ∀ {A : Type u} [CommRing A] [IsDomain A], ringKrullDim A = 1 →
      ∀ p : PrimeSpectrum A, PrimeSpectrum.quotientKrullDim p = 1 ↔ p = ⊥)

/- Example 42.7.3 (4): on a one-dimensional domain, the quotient Krull dimension is a
dimension function. -/
@[stacks 02QN] #check
  (PrimeSpectrum.quotientKrullDim.isDimensionFunctionOfDimOneDomain :
    ∀ {A : Type u} [CommRing A] [IsDomain A], ringKrullDim A = 1 →
      IsDimensionFunction (PrimeSpectrum.quotientKrullDim : PrimeSpectrum A → ℤ))

/- The integers give the illustrative one-dimensional domain. -/
#check
  (IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField : ringKrullDim ℤ = 1)
