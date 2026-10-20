module

public import ReasLib.Algebra.WLocalHull.AlongClosed

/-!
# Specializing localization of the w-localization along a closed stratum

The ring obtained by first forming the w-localization `A_w` and then
specializing along `V(I A_w)`.
-/

@[expose] public section

universe u

open Algebra.WLocalHull

#check (Algebra.WLocalHull.alongClosed :
  (A : Type u) → [CommRing A] → Ideal A → Type u)

#check (Algebra.WLocalHull.alongClosed_indZariski :
  ∀ (A : Type u) [CommRing A] (I : Ideal A),
    (algebraMap A (alongClosed A I)).IndZariski)

#check (Algebra.WLocalHull.instWLocalSpace_alongClosed :
  ∀ (A : Type u) [CommRing A] (I : Ideal A)
    [TotallyDisconnectedSpace (PrimeSpectrum.zeroLocus (I : Set A))],
    WLocalSpace (PrimeSpectrum (alongClosed A I)))

#check (Algebra.WLocalHull.closedPoints_alongClosed :
  ∀ (A : Type u) [CommRing A] (I : Ideal A)
    [TotallyDisconnectedSpace (PrimeSpectrum.zeroLocus (I : Set A))],
    closedPoints (PrimeSpectrum (alongClosed A I)) =
      PrimeSpectrum.zeroLocus (I.map (algebraMap A (alongClosed A I)) : Set (alongClosed A I)))

#check (Algebra.WLocalHull.bijective_quotientMap_alongClosed :
  ∀ (A : Type u) [CommRing A] (I : Ideal A)
    [TotallyDisconnectedSpace (PrimeSpectrum.zeroLocus (I : Set A))],
    Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A (alongClosed A I)))
        (algebraMap A (alongClosed A I)) Ideal.le_comap_map))
