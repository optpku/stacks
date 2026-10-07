module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Extension.ExtendScalars
public import ReasLib.RingTheory.Extension.Cotangent.Surjective

/-!
# Connecting map of the extended conormal sequence

For a tower of commutative algebras `R → S → T` with `S → T` surjective, the first arrow of
the extended naive-cotangent sequence is the `S`-linear composite of `H1Cotangent.map`,
the surjective identification `equivOfSurjective`, and `cotangentEquivCotangentKer`.
-/

@[expose] public section

universe u

open Algebra.Extension

namespace Algebra.H1Cotangent

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- The connecting map `H1Cotangent R T →ₗ[S] (ker (algebraMap S T)).Cotangent` of the
extended conormal sequence, for a surjective algebra map `S → T`. -/
noncomputable def toConormal (h : Function.Surjective (algebraMap S T)) :
    H1Cotangent R T →ₗ[S] (RingHom.ker (algebraMap S T)).Cotangent :=
  let P := ofSurjective (Algebra.ofId S T) h
  (P.cotangentEquivCotangentKer.restrictScalars S).toLinearMap ∘ₗ
    (equivOfSurjective h).restrictScalars S ∘ₗ (map R S T T).restrictScalars S

/-- `toConormal` is the composite of `H1Cotangent.map`, `equivOfSurjective`, and
`cotangentEquivCotangentKer`. -/
theorem toConormal_apply (h : Function.Surjective (algebraMap S T)) (x : H1Cotangent R T) :
    toConormal R S T h x =
      (ofSurjective (Algebra.ofId S T) h).cotangentEquivCotangentKer
        (equivOfSurjective h (map R S T T x)) := sorry

/-- The extended conormal sequence is exact at `(ker (algebraMap S T)).Cotangent`. -/
theorem exact_toConormal_kerCotangentToTensor (h : Function.Surjective (algebraMap S T)) :
    Function.Exact (toConormal R S T h) (KaehlerDifferential.kerCotangentToTensor R S T) := sorry

end Algebra.H1Cotangent
