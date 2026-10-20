module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Connected.TotallyDisconnected
public import ReasLib.Algebra.WLocalHull.WLocalization
public import ReasLib.RingTheory.Localization.Specializing
public import ReasLib.Topology.WLocal
public import ReasLib.RingTheory.RingHom.IndZariski

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

/-- When `V(I)` is totally disconnected, the closed points of
`Spec(alongClosed A I)` are `V(I · alongClosed A I)`. -/
theorem closedPoints_alongClosed
    [TotallyDisconnectedSpace (PrimeSpectrum.zeroLocus (I : Set A))] :
    closedPoints (PrimeSpectrum (alongClosed A I)) =
      PrimeSpectrum.zeroLocus (I.map (algebraMap A (alongClosed A I)) : Set (alongClosed A I)) :=
  sorry

/-- When `V(I)` is totally disconnected, the canonical map
`A ⧸ I → alongClosed A I ⧸ I.map (algebraMap A (alongClosed A I))` is bijective. -/
theorem bijective_quotientMap_alongClosed
    [TotallyDisconnectedSpace (PrimeSpectrum.zeroLocus (I : Set A))] :
    Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A (alongClosed A I)))
        (algebraMap A (alongClosed A I)) Ideal.le_comap_map) :=
  sorry

/-- A profinite closed locus `V(I)` admits an ind-Zariski extension with w-local
prime spectrum, closed points `V(IB)`, and bijective canonical quotient map
`A ⧸ I → B ⧸ IB`. -/
theorem exists_alongClosed
    [CompactSpace (PrimeSpectrum.zeroLocus (I : Set A))]
    [T2Space (PrimeSpectrum.zeroLocus (I : Set A))]
    [TotallyDisconnectedSpace (PrimeSpectrum.zeroLocus (I : Set A))] :
    ∃ (B : Type u) (ringB : CommRing B) (f : A →+* B),
      f.IndZariski ∧ WLocalSpace (PrimeSpectrum B) ∧
        closedPoints (PrimeSpectrum B) = PrimeSpectrum.zeroLocus (I.map f : Set B) ∧
        Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) := by
  exact ⟨alongClosed A I, inferInstance, algebraMap A (alongClosed A I),
    alongClosed_indZariski A I, instWLocalSpace_alongClosed A I,
    closedPoints_alongClosed A I, bijective_quotientMap_alongClosed A I⟩

end Algebra.WLocalHull
