module

public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.Topology.Connected.Separation
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import ReasLib.RingTheory.KrullDimension.FiniteType
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Zero-dimensional finite-type algebras over fields

This leaf owns the equivalent zero-dimensionality criteria and the two narrow
consequences needed by regular-element arguments.  Keeping the criteria in the
`Algebra.FiniteType` namespace shortens names and removes chapter dependencies.

@stack 0ALW
@stack 0GEC
-/

universe u v

namespace Algebra.FiniteType

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable [Algebra.FiniteType k S]

include k

/-- Lemma 10.61.3 (Tag 0ALW): for a finite-type algebra over a field, zero-dimensionality,
finiteness and separation properties of the prime spectrum, finite-dimensionality, the Artinian
property, and discreteness of the prime spectrum are equivalent. -/
@[stacks 0ALW]
theorem zeroDimensionalTFAE :
    List.TFAE
      [ Ring.KrullDimLE 0 S,
        Finite (PrimeSpectrum S),
        Finite (MaximalSpectrum S),
        T2Space (PrimeSpectrum S),
        FiniteDimensional k S,
        IsArtinianRing S,
        DiscreteTopology (PrimeSpectrum S) ] := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have hFiniteType : (algebraMap k S).FiniteType := by
    rwa [RingHom.finiteType_algebraMap]
  letI : IsJacobsonRing S := hFiniteType.isJacobsonRing
  have hclosedPoints_of_finiteMax [Finite (MaximalSpectrum S)] :
      (closedPoints (PrimeSpectrum S)).Finite := by
    let f : MaximalSpectrum S → closedPoints (PrimeSpectrum S) := fun x ↦
      ⟨x.toPrimeSpectrum, (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr x.isMaximal⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      exact ⟨⟨x.asIdeal, (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx⟩, rfl⟩
    exact Finite.of_surjective f hf
  tfae_have 1 ↔ 5 := by
    simpa using (Module.finite_iff_krullDimLE_zero k S).symm
  tfae_have 5 ↔ 6 := by
    simpa using Module.finite_iff_isArtinianRing k S
  tfae_have 6 → 3 := by
    intro hArt
    letI : IsArtinianRing S := hArt
    infer_instance
  tfae_have 3 → 7 := by
    intro hfin
    letI : Finite (MaximalSpectrum S) := hfin
    exact JacobsonSpace.discreteTopology hclosedPoints_of_finiteMax
  tfae_have 6 ↔ 7 := by
    constructor
    · intro hArt
      letI : IsArtinianRing S := hArt
      letI : Finite (MaximalSpectrum S) := inferInstance
      exact JacobsonSpace.discreteTopology hclosedPoints_of_finiteMax
    · intro hdisc
      exact
        (Module.finite_iff_isArtinianRing k S).mp <|
          (Module.finite_iff_krullDimLE_zero k S).mpr <|
            (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hdisc).2
  tfae_have 7 → 2 := by
    intro hdisc
    exact (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hdisc).1
  tfae_have 2 → 4 := by
    intro hfin
    letI : Finite (PrimeSpectrum S) := hfin
    let hclosed : (closedPoints (PrimeSpectrum S)).Finite := Set.toFinite _
    letI : DiscreteTopology (PrimeSpectrum S) := JacobsonSpace.discreteTopology hclosed
    infer_instance
  tfae_have 4 → 1 := by
    intro hT2
    letI : T2Space (PrimeSpectrum S) := hT2
    letI : T1Space (PrimeSpectrum S) := T2Space.t1Space
    refine Ring.KrullDimLE.mk₀ fun I hI ↦ ?_
    exact
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal ⟨I, hI⟩).mp
        isClosed_singleton
  tfae_finish

/-- Finite maximal spectrum is the owner-level zero-dimensionality criterion for a finite-type
algebra over a field. -/
@[stacks 0ALW "finite maximal spectrum criterion"]
theorem finiteMaximalSpectrum_iff_krullDimLE_zero :
    Finite (MaximalSpectrum S) ↔ Ring.KrullDimLE 0 S := by
  simpa using ((zeroDimensionalTFAE (k := k) (S := S)).out 0 2 rfl rfl).symm

/-- The maximal spectrum is infinite exactly when the finite-type algebra is not
zero-dimensional.  This is the negative, instance-producing form of
`finiteMaximalSpectrum_iff_krullDimLE_zero`. -/
@[stacks 0ALW "infinite maximal spectrum criterion"]
theorem infiniteMaximalSpectrum_iff_not_krullDimLE_zero :
    Infinite (MaximalSpectrum S) ↔ ¬ Ring.KrullDimLE 0 S := by
  rw [← not_finite_iff_infinite,
    not_congr (finiteMaximalSpectrum_iff_krullDimLE_zero (k := k) (S := S))]

/-- Positive Krull dimension forces the maximal spectrum of a finite-type algebra over a field
to be infinite.  No `Nontrivial S` parameter is required because positivity already excludes the
zero ring. -/
theorem infiniteMaximalSpectrum_of_pos_ringKrullDim (hdim : 0 < ringKrullDim S) :
    Infinite (MaximalSpectrum S) := by
  rw [infiniteMaximalSpectrum_iff_not_krullDimLE_zero (k := k) (S := S)]
  intro hdim_zero
  letI : Nontrivial S := by
    by_contra hS
    letI : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS
    simp [ringKrullDim_eq_bot_of_subsingleton] at hdim
  exact not_lt_of_ge
    (ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hdim_zero).le hdim

/-- Lemma 10.63.20 (Tag 0GEC): a positive-dimensional finite-type algebra over a field contains
a non-zero-divisor that is not a unit. -/
@[stacks 0GEC]
theorem exists_nonZeroDivisor_nonunit_of_pos_ringKrullDim (hdim : 0 < ringKrullDim S) :
    ∃ f : S, f ∈ nonZeroDivisors S ∧ ¬ IsUnit f := sorry

end Algebra.FiniteType
