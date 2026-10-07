module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.Henselian.StrictHenselian
public import ReasLib.RingTheory.RingHom.IndEtale.Basic
public import stacks_project.Chap61.Definition_61_2_3_WLocal
public import stacks_project.Chap61.Lemma_61_5_7_AlongClosed
public import stacks_project.Chap61.Lemma_61_8_1_Iterate

/-!
# W-local faithfully flat ind-étale covers

The cover of a commutative ring `A` obtained by w-localizing, iterating the
ind-étale envelope, and specializing along the closed-points ideal of the
w-localization.
-/

@[expose] public section

universe u

open Algebra.WLocalHull Algebra.IndEtaleEnvelope

namespace Algebra.WLocalIndEtale

/-- The vanishing ideal of the closed points of `PrimeSpectrum R`. -/
noncomputable def closedPointsIdeal (R : Type u) [CommRing R] : Ideal R :=
  PrimeSpectrum.vanishingIdeal (closedPoints (PrimeSpectrum R))

/-- On a w-local affine spectrum, the zero locus of `closedPointsIdeal R` is the
set of closed points. -/
theorem zeroLocus_closedPointsIdeal (R : Type u) [CommRing R]
    [WLocalSpace (PrimeSpectrum R)] :
    PrimeSpectrum.zeroLocus (closedPointsIdeal R : Set R) =
      closedPoints (PrimeSpectrum R) :=
  sorry

/-- The closed-points ideal of `wLocalization A`, extended to
`Iteration (wLocalization A)`. -/
noncomputable def coverIdeal (A : Type u) [CommRing A] :
    Ideal (Iteration (wLocalization A)) :=
  (closedPointsIdeal (wLocalization A)).map
    (algebraMap (wLocalization A) (Iteration (wLocalization A)))

/-- The w-local faithfully flat ind-étale cover of `A`. -/
noncomputable def Cover (A : Type u) [CommRing A] : Type u :=
  alongClosed (Iteration (wLocalization A)) (coverIdeal A)

/-- The commutative ring structure on `Cover A` transported from
`alongClosed`. -/
noncomputable instance instCommRing (A : Type u) [CommRing A] : CommRing (Cover A) :=
  inferInstanceAs (CommRing (alongClosed (Iteration (wLocalization A)) (coverIdeal A)))

/-- `Cover A` is an algebra over the iterated envelope of `wLocalization A`. -/
noncomputable instance instAlgebra_iteration (A : Type u) [CommRing A] :
    Algebra (Iteration (wLocalization A)) (Cover A) :=
  inferInstanceAs
    (Algebra (Iteration (wLocalization A))
      (alongClosed (Iteration (wLocalization A)) (coverIdeal A)))

/-- The structure map `A → Cover A` through w-localization and ind-étale
iteration. -/
noncomputable instance instAlgebra (A : Type u) [CommRing A] : Algebra A (Cover A) :=
  RingHom.toAlgebra
    ((algebraMap (Iteration (wLocalization A)) (Cover A)).comp
      ((algebraMap (wLocalization A) (Iteration (wLocalization A))).comp
        (algebraMap A (wLocalization A))))

/-- The `A`-algebra map of `Cover A` is the composite through `wLocalization A`
and `Iteration (wLocalization A)`. -/
theorem algebraMap_eq (A : Type u) [CommRing A] :
    algebraMap A (Cover A) =
      (algebraMap (Iteration (wLocalization A)) (Cover A)).comp
        ((algebraMap (wLocalization A) (Iteration (wLocalization A))).comp
          (algebraMap A (wLocalization A))) :=
  sorry

/-- `Cover A` is faithfully flat as an `A`-algebra. -/
instance instFaithfullyFlat (A : Type u) [CommRing A] :
    Module.FaithfullyFlat A (Cover A) :=
  sorry

/-- The structure map `A → Cover A` is faithfully flat. -/
theorem algebraMap_faithfullyFlat (A : Type u) [CommRing A] :
    (algebraMap A (Cover A)).FaithfullyFlat :=
  sorry

/-- The structure map `A → Cover A` is ind-étale. -/
theorem indEtale (A : Type u) [CommRing A] :
    (algebraMap A (Cover A)).IndEtale :=
  sorry

/-- `PrimeSpectrum (Cover A)` is a w-local space. -/
instance instWLocalSpace (A : Type u) [CommRing A] :
    WLocalSpace (PrimeSpectrum (Cover A)) :=
  sorry

/-- Closed points of `PrimeSpectrum (Cover A)` surject onto `PrimeSpectrum A`. -/
theorem surjOn_closedPoints (A : Type u) [CommRing A] :
    Set.SurjOn (PrimeSpectrum.comap (algebraMap A (Cover A)))
      (closedPoints (PrimeSpectrum (Cover A))) Set.univ :=
  sorry

/-- Localizations of `Cover A` at maximal ideals are strictly henselian. -/
instance instStrictHenselianLocalRing (A : Type u) [CommRing A]
    (m : Ideal (Cover A)) [m.IsMaximal] :
    StrictHenselianLocalRing (Localization.AtPrime m) :=
  sorry

end Algebra.WLocalIndEtale
