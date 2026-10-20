/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.Artinian
public import ReasLib.RingTheory.Ideal.GoingDown
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Polynomial
public import ReasLib.RingTheory.KrullDimension.FiniteType.DimensionFormula
public import ReasLib.RingTheory.Completion.FaithfullyFlat
public import ReasLib.Algebra.Module.MatlisDuality.Artinian
import StacksCheckRecall

@[expose] public section

universe u v w

open IsLocalRing

/- Exercise 111.64.2 (Theorems) (1): a commutative ring is Artinian iff it is Noetherian of
Krull dimension at most 0. -/
@[stacks 0GRU] #check
  (Ring.KrullDimension.isArtinianRing_iff_isNoetherianRing_krullDimLE_zero :
    ∀ {R : Type u} [CommRing R],
      IsArtinianRing R ↔ IsNoetherianRing R ∧ Ring.KrullDimLE 0 R)

/- Exercise 111.64.2 (Theorems) (2): a flat algebra satisfies going down for prime ideals. -/
@[stacks 0GRU] #check
  (Algebra.HasGoingDown.of_flatModule :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [Module.Flat R S], Algebra.HasGoingDown R S)

/- Exercise 111.64.2 (Theorems) (3): for a Noetherian local ring, the Hilbert–Samuel χ-polynomial
eventually equals the lengths of M / m^{n+1} M. -/
@[stacks 0GRU] #check
  (Ideal.HilbertSamuel.chiPolynomial_spec_maximalIdeal :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
      (Ideal.HilbertSamuel.chiPolynomial (maximalIdeal R) M).EventuallyEqNat
        (fun n ↦ ((Ideal.hilbertSamuelChi (maximalIdeal R) M n).toNat : ℚ)))

/- Exercise 111.64.2 (Theorems) (4): the dimension formula for an injective finite-type map of
domains over a universally catenary Noetherian ring. -/
@[stacks 0GRU] #check
  (PrimeSpectrum.height_add_residueFieldTrdeg_eq_of_universallyCatenary :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
      [Algebra R S] [Algebra.FiniteType R S] [UniversallyCatenaryRing.{u, v} R]
      (hinj : Function.Injective (algebraMap R S)) (q : PrimeSpectrum S),
      ENat.toNat (Ideal.height q.asIdeal) +
          Cardinal.toNat (Ideal.ResidueField.trdeg (q.asIdeal.under R) q.asIdeal) =
        ENat.toNat (Ideal.height (q.asIdeal.under R)) + FractionRing.trdegNatOf hinj)

/- Exercise 111.64.2 (Theorems) (5): the maximal-ideal adic completion of a Noetherian local
ring is faithfully flat. -/
@[stacks 0GRU] #check
  (AdicCompletion.maximalIdeal_algebraMap_faithfullyFlat :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
      RingHom.FaithfullyFlat (algebraMap R (AdicCompletion (maximalIdeal R) R)))

/- Exercise 111.64.2 (Theorems) (6): finite modules over an Artinian local ring are reflexive
relative to an injective hull of the residue field. -/
@[stacks 0GRU] #check
  (Module.isReflexiveRelativeTo_of_injectiveHull :
    ∀ (R : Type u) (E : Type v) (M : Type w) [CommRing R] [IsLocalRing R]
      [IsArtinianRing R] [AddCommGroup E] [Module R E] [Module.Injective R E]
      [AddCommGroup M] [Module R M] [Module.Finite R M]
      (ι : ResidueField R →ₗ[R] E),
      ι.IsInjectiveHull → Module.IsReflexiveRelativeTo R E M)
