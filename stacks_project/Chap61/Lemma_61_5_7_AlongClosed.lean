/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Connected.TotallyDisconnected
public import stacks_project.Chap61.Definition_61_2_3_WLocal
public import stacks_project.Chap61.Definition_61_4_1_IndZariski
public import stacks_project.Chap61.Lemma_61_5_1_Localization
public import stacks_project.Chap61.«61_5_2_5_WLocalization»

/-!
# Specializing localization of the w-localization along a closed stratum

The ring obtained by first forming the w-localization `A_w` and then
specializing along `V(I A_w)`.
-/

@[expose] public section

universe u

namespace Algebra.WLocalHull

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The ring obtained by w-localizing `A` and then specializing along the closed
stratum `V(I A_w)`. -/
abbrev alongClosed : Type u :=
  Localization.specializing (1 : wLocalization A) (I.map (algebraMap A (wLocalization A)))

/-- The structure map `A → alongClosed A I` is ind-Zariski. -/
theorem alongClosed_indZariski : (algebraMap A (alongClosed A I)).IndZariski :=
  sorry

/-- The prime spectrum of `alongClosed A I` is w-local when `V(I)` is totally
disconnected. -/
instance instWLocalSpace_alongClosed
    [TotallyDisconnectedSpace (PrimeSpectrum.zeroLocus (I : Set A))] :
    WLocalSpace (PrimeSpectrum (alongClosed A I)) :=
  sorry

/-- The closed points of `Spec(alongClosed A I)` are `V(I · alongClosed A I)`. -/
theorem closedPoints_alongClosed
    [TotallyDisconnectedSpace (PrimeSpectrum.zeroLocus (I : Set A))] :
    closedPoints (PrimeSpectrum (alongClosed A I)) =
      PrimeSpectrum.zeroLocus (I.map (algebraMap A (alongClosed A I)) : Set (alongClosed A I)) :=
  sorry

/-- The canonical map `A ⧸ I → alongClosed A I ⧸ I.map (algebraMap A (alongClosed A I))`
is bijective. -/
theorem bijective_quotientMap_alongClosed
    [TotallyDisconnectedSpace (PrimeSpectrum.zeroLocus (I : Set A))] :
    Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A (alongClosed A I)))
        (algebraMap A (alongClosed A I)) Ideal.le_comap_map) :=
  sorry

end Algebra.WLocalHull
