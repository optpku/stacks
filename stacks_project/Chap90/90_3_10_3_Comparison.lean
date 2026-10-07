module

public import ReasLib.RingTheory.Kaehler.ExtendedConormal

/-!
# Common-k comparison maps for the extended conormal sequence

The canonical comparison maps and their exactness and naturality laws are
provided by the extended conormal sequence owner.
-/

@[expose] public section

open Algebra

universe u v w

#check (Algebra.H1Cotangent.toKerCotangent :
  ∀ (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra Λ k] [Algebra A k] [IsScalarTower Λ A k]
    (h : Function.Surjective (algebraMap A k)),
    H1Cotangent Λ k →ₗ[k] (Extension.ofSurjective (Algebra.ofId A k) h).Cotangent)
