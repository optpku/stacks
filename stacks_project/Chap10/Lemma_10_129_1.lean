/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.KrullDimension.Equidimensional
public import ReasLib.Topology.KrullDimension.Local
public import ReasLib.RingTheory.Ideal.Quotient.PrimeSpectrum
public import ReasLib.RingTheory.KrullDimension.FiniteType.Local
public import ReasLib.RingTheory.CohenMacaulay.Ring
public import ReasLib.RingTheory.CohenMacaulay.RegularSequence
import StacksCheckRecall

@[expose] public section

/-! @stack 00R9

The quotient-spectrum and zero-locus maps below are source-facing bridges to the canonical
`PrimeSpectrum.quotientOfLE` owner.  The labeled theorem keeps the
expected-codimension and localized-regular-sequence clauses on the canonical `PrimeSpectrum` and
`Localization.AtPrime` carriers.
-/

universe u v

open RingTheory Sequence

section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
variable [CohenMacaulayRing S] [TopologicalSpace.EquidimensionalSpace (PrimeSpectrum S)]

@[stacks 00R9 "quotient-prime bridge"]
#check @PrimeSpectrum.quotientOfLE

@[stacks 00R9 "quotient-prime ideal"]
#check @PrimeSpectrum.quotientOfLE_asIdeal

@[stacks 00R9 "quotient-prime contraction"]
#check @PrimeSpectrum.quotientOfLE_comap_asIdeal

@[stacks 00R9 "quotient-prime complement"]
#check @PrimeSpectrum.quotientOfLE_primeCompl

include k

/-- Chap10 Lemma 10 129 1: for a finite list `fs` in a Cohen--Macaulay equidimensional finite-type
`k`-algebra `S`, an expected-codimension bound for `V(Ideal.ofList fs)` gives equality whenever
the list ideal is proper; at every prime containing that ideal, the image of `fs` in
`Localization.AtPrime q.asIdeal` is a regular sequence. -/
@[stacks 00R9]
theorem ringKrullDim_quotient_add_length_eq_and_isRegular_atPrime_of_cohenMacaulay_equidimensional
    {fs : List S}
    (hzero :
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) + fs.length ≤
        ringKrullDim S) :
    (Ideal.ofList fs ≠ ⊤ →
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) + fs.length =
        ringKrullDim S) ∧
      ∀ q : PrimeSpectrum S, Ideal.ofList fs ≤ q.asIdeal →
        IsRegular (Localization.AtPrime q.asIdeal)
          (fs.map (algebraMap S (Localization.AtPrime q.asIdeal))) := sorry

end
