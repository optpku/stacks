module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Normal.Local

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The spectrum of a two-dimensional Noetherian complete normal local ring admits a
resolution of singularities. -/
theorem existsResolution_of_completeNormalLocalDomain
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] [IsNormalRing A]
    (h_dimension : ringKrullDim A = 2) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f := sorry

end AlgebraicGeometry.Scheme
