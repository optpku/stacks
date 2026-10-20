module

public import ReasLib.Topology.ConnectedComponents.Generalization
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.Topology.Noetherian.Basic

/-!
# Connected components of prime spectra

Connected components of Noetherian prime spectra are open. The spectrum of a countable
product of two-element fields has infinitely many closed points and a nonopen component.
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- Connected components of the prime spectrum of a Noetherian semiring are open. -/
theorem isOpen_connectedComponent_of_isNoetherianRing {R : Type u} [CommSemiring R]
    [IsNoetherianRing R] (x : PrimeSpectrum R) :
    IsOpen (connectedComponent x) := sorry

/-- A maximal connected subset of the prime spectrum of a Noetherian semiring is open. -/
theorem isOpen_of_maximal_isConnected_of_isNoetherianRing {R : Type u} [CommSemiring R]
    [IsNoetherianRing R] {T : Set (PrimeSpectrum R)} (hT : Maximal IsConnected T) :
    IsOpen T := sorry

/-- On `Spec(ℕ → ZMod 2)`, every point is closed. -/
theorem closedPoints_eq_univ_piZModTwo :
    closedPoints (PrimeSpectrum (ℕ → ZMod 2)) = Set.univ := sorry

/-- `Spec(ℕ → ZMod 2)` has infinitely many closed points. -/
theorem infinite_closedPoints_piZModTwo :
    (closedPoints (PrimeSpectrum (ℕ → ZMod 2))).Infinite := sorry

/-- The prime spectrum of a countable product of two-element fields has a connected component
that is not open. -/
theorem exists_connectedComponent_not_isOpen_piZModTwo :
    ∃ x : PrimeSpectrum (ℕ → ZMod 2), ¬ IsOpen (connectedComponent x) := sorry

end PrimeSpectrum
