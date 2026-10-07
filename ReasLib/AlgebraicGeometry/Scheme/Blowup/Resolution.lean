module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.Normal.Local
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedSequence

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A two-dimensional Noetherian normal local ring whose spectrum has a resolution
admits a resolution by normalized blowups. -/
theorem hasResolutionByNormalizedBlowups_of_existsResolution
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalRing A]
    (h_dim : ringKrullDim A = 2)
    (h_resolution :
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f) :
    HasResolutionByNormalizedBlowups (Spec (.of A))
      ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans h_dim) := sorry

end AlgebraicGeometry.Scheme
