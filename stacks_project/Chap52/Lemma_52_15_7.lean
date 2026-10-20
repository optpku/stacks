/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap52.Proposition_52_12_3
public import stacks_project.Chap52.Lemma_52_15_2
public import stacks_project.Chap52.«52_8_0_1_AssociatedSubset»
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import ReasLib.RingTheory.Ideal.Localization
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.AssociatedPrimeCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

/- Lemma 52.15.7 -/
@[stacks 0EKU] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.neighborhoodCompletionFullyFaithful_of_associatedPrimeDimension :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
      (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
      [IsAdicComplete S.I A]
      (h_dimension : ∀ p q : PrimeSpectrum A,
        p.asIdeal ∈ associatedPrimes A A →
          ¬ S.I ≤ p.asIdeal →
            p ∉ PrimeSpectrum.associatedSubset S.I S.a →
              q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                PrimeSpectrum.zeroLocus (S.a : Set A) →
                ((Ideal.LocalCohomology.dimension S.I
                    S.I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                  WithBot.map (WithTop.map Int.ofNat)
                    (ringKrullDim (p.asIdeal.quotientAtPrime q))),
      CoherentCompletion.NeighborhoodCompletionFullyFaithful
        (AffineAlgebraizationSetup.idealOnOpen S))
