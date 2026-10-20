module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.CompleteIntersection.Fiber

@[expose] public section

universe u

open AlgebraicGeometry

namespace RingHom

namespace FiniteTypeCounterexample

/-- There is a flat finite-type ring map that is not finitely presented and has geometrically
irreducible global complete-intersection fibers at every prime of the source. -/
theorem exists_irreducibleFibers :
    ∃ (R S : Type u) (_ : CommRing R) (_ : CommRing S) (f : R →+* S),
      f.Flat ∧ f.FiniteType ∧ ¬f.FinitePresentation ∧
        GeometricallyIrreducible (Spec.map (CommRingCat.ofHom f)) ∧
          ∀ p : PrimeSpectrum R, Fiber.IsGlobalCompleteIntersection f p.asIdeal := sorry

/-- There is a flat finite-type ring map that is not finitely presented and has geometrically
connected, geometrically reduced, one-dimensional global complete-intersection fibers at every
prime of the source. -/
theorem exists_connectedReducedFibers :
    ∃ (R S : Type u) (_ : CommRing R) (_ : CommRing S) (f : R →+* S),
      f.Flat ∧ f.FiniteType ∧ ¬f.FinitePresentation ∧
        GeometricallyConnected (Spec.map (CommRingCat.ofHom f)) ∧
          GeometricallyReduced (Spec.map (CommRingCat.ofHom f)) ∧
            (∀ p : PrimeSpectrum R, ringKrullDim (f.Fiber p.asIdeal) = 1) ∧
              ∀ p : PrimeSpectrum R, Fiber.IsGlobalCompleteIntersection f p.asIdeal := sorry

end FiniteTypeCounterexample

end RingHom
