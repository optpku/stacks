module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Purity
public import ReasLib.RingTheory.Smooth.Adic.Basic
public import ReasLib.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme

variable {A B : Type u} [CommRing A] [CommRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- For a local homomorphism of Noetherian local rings with source depth at least
two, formal smoothness for the target maximal-ideal-adic topology, and strictly
larger target Krull dimension, finite étale restriction is an equivalence on any
open containing all primes outside the closed fiber and the prime given by the
extension of the source maximal ideal. -/
theorem finiteEtaleBaseChange_isEquivalence_of_formallySmoothDepth
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A)
    (hfs : (algebraMap A B).formally_smooth_for_adic (IsLocalRing.maximalIdeal B))
    (hdim : ringKrullDim A < ringKrullDim B)
    (V : (Spec (CommRingCat.of B)).Opens)
    (hV : ∀ q : PrimeSpectrum B,
      Ideal.comap (algebraMap A B) q.asIdeal ≠ IsLocalRing.maximalIdeal A ∨
        q.asIdeal = Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) →
      q ∈ V) :
    Functor.IsEquivalence (finiteEtaleBaseChange V.ι) := sorry

end AlgebraicGeometry.Scheme
